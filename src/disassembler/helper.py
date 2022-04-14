# Concolic model checker
# Copyright (C) <2021> <Xiaoxin An> <Virginia Tech>

# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.

# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.

# You should have received a copy of the GNU General Public License
# along with this program.  If not, see <https://www.gnu.org/licenses/>.

import re
import os

from ..common import utils


UNEXPLORED_FUNCTION_LABELS = {'_init', '_fini', '__libc_csu_init', '__libc_csu_fini', 
'frame_dummy', 'register_tm_clones', 'deregister_tm_clones', '__do_global_dtors_aux'}


BYTE_LEN_REPS = {
    'byte': 'byte', 
    'dword': 'dword', 
    'fword': 'fword', 
    'qword': 'qword', 
    'word': 'word', 
    'tbyte': 'tbyte',
    'tword': 'tbyte', 
    'xword': 'tbyte',
    'xmmword': 'xmmword'
}


BYTE_REP_PTR_MAP = {
    'q': 'qword ptr',
    'd': 'dword ptr',
    'l': 'dword ptr',
    'w': 'word ptr',
    'b': 'byte ptr',
    't': 'tbyte ptr'
}

BYTELEN_REP_MAP = {
    64: 'qword ptr',
    32: 'dword ptr',
    16: 'word ptr',
    8: 'byte ptr'
}

simple_operator_pat = re.compile(r'(\+|-|\*)')
remote_addr_pat = re.compile('0x2[0-9a-fA-F]{5}')


def disassemble_to_asm(disasm_path):
    if os.path.exists(disasm_path): return
    else:
        raise Exception('The assembly file has not been generated')


def convert_to_hex(line):
    if re.match(r'^[0-9a-f]+$', line):
        return '0x' + line.strip()
    return line


def to_hex(num, bits):
    return hex((num + (1 << bits)) % (1 << bits))


def calculate_relative_address(line, address):
    if re.match(r'^0x[0-9a-f]+$|^[0-9a-f]+$', line):
        relative_address = int(line, 16) - address
        if relative_address >= 0:
            line = '0x{0:X}'.format(relative_address)
        else:
            line = str(to_hex(relative_address, 64))
    return line


def calculate_absolute_address(line, rip):
    if re.match(r'^0x[0-9a-f]+$|^-0x[0-9a-f]+$', line):
        absolute_address = int(line, 16) + rip
        if absolute_address >= 0:
            line = '0x{0:x}'.format(absolute_address)
        else:
            line = str(to_hex(absolute_address, 64))
    return line


def check_section_start(line, disassembler='objdump'):
    result = False
    if disassembler == 'objdump':
        result = line.startswith('Disassembly of section')
    return result


def normalize_arg(address, name, arg):
    res = re.sub(r'[+-]0x0\b|\*1\b', '', arg)
    if utils.check_jmp_with_address(name):
        res = calculate_relative_address(res, address)
    return res


def remove_att_prefix(arg):
    res = arg
    if arg.startswith('%'):
        res = arg.split('%', 1)[1].strip()
    elif arg.startswith('*%'):
        res = arg.split('*%', 1)[1].strip()
    elif arg.startswith(('$0x', '$-0x')):
        res = arg.split('$', 1)[1].strip()
    return res


def reconstruct_att_memory_rep(inst_name, arg):
    res = '['
    arg_split = arg.split('(', 1)
    arg_split_1 = arg_split[1].strip().rsplit(')', 1)[0].split(',')
    arg_split_1_0 = arg_split_1[0].strip()
    res += remove_att_prefix(arg_split_1_0)
    if len(arg_split_1) > 1:
        if arg_split_1_0:
            res += '+'
        res += remove_att_prefix(arg_split_1[1])
        if len(arg_split_1) == 3:
            res += '*' + remove_att_prefix(arg_split_1[2])
    if arg_split[0].strip():
        res += '+' + remove_att_prefix(arg_split[0].strip())
    res += ']'
    return res

def rewrite_att_memory_rep(inst_name, arg):
    res = arg
    if arg.startswith('*'):
        arg = arg.split('*', 1)[1].strip()
    if '(' in arg:  #%cs:(%rax,%rax)
        if '%st' in arg:
            res = arg.split('%', 1)[1].strip()
        elif ':' in arg:
            arg_split = arg.split(':')
            res = remove_att_prefix(arg_split[0]) + ':'
            res += reconstruct_att_memory_rep(inst_name, arg_split[1].strip())
        else:
            res = reconstruct_att_memory_rep(inst_name, arg)
    elif ':' in arg:    #%fs:0x28
        arg_split = arg.split(':')
        res = remove_att_prefix(arg_split[0]) + ':' + remove_att_prefix(arg_split[1])
    else:
        res = remove_att_prefix(arg)
    if res.endswith(']'):
        res = res.replace('+-', '-')
    return res


def rewrite_absolute_address_to_relative(arg, rip):
    res = arg
    if arg.endswith(']') and 's:' not in arg:
        arg_split = arg.strip().split('[')
        arg_content = arg_split[1].split(']')[0].strip()
        if re.match(r'^0x[0-9a-f]+$|^-0x[0-9a-f]+$', arg_content):
            relative_address = int(arg_content, 16) - rip
            if relative_address >= 0:
                res = '[rip+0x{0:x}]'.format(relative_address)
            else:
                res = '[rip+' + str(to_hex(relative_address, utils.MEM_ADDR_SIZE)) + ']'
            if arg.startswith(('qword', 'dword', 'word', 'byte', 'tbyte', 'xmmword')):
                res = arg_split[0] + res
    elif re.match(r'^0x[0-9a-f]+$|^-0x[0-9a-f]+$', arg):
        res = hex(utils.imm_str_to_int(arg))
    return res


def add_ptr_suffix_arg(arg):
    res = arg
    if arg.endswith(']') and ' ptr ' not in arg:
        b_len_rep = arg.split(' ', 1)[0].strip()
        if b_len_rep in BYTE_LEN_REPS:
            res = re.sub(b_len_rep, BYTE_LEN_REPS[b_len_rep] + ' ptr', arg)
    return res


def add_or_remove_ptr_rep_arg(inst_name, arg):
    res = arg
    if inst_name.startswith('rep') and ('cmpsb' in inst_name or 'scasb' in inst_name) and ']' in arg:
        res = '[' + arg.rsplit('[', 1)[1].strip()
    else:
        res = add_ptr_suffix_arg(arg)
    return res

def convert_to_hex_rep(arg):
    res = arg
    if re.match(r'^[0-9a-f]+$|^-[0-9a-f]+$', arg):
        res = hex(int(arg, 16))
    return res


def norm_objdump_arg(name, arg):
    res = arg
    if name == 'fdivrp' and arg == 'st':
        res = 'st(0)'
    return res


def init_ida_struct_info():
    ida_struct_table = {}
    ida_info_path = os.path.join(utils.PROJECT_DIR, 'ida_struct.info')
    with open(ida_info_path, 'r') as f:
        lines = f.readlines()
        for line in lines:
            line = line.strip()
            if line and not line.startswith('#'):
                line_split = line.split(':', 1)
                if line_split[1]:
                    item_name = line_split[0]
                    offset_str, item_type = line_split[1].strip().split(',', 1)
                    offset = int(offset_str.strip())
                    ida_struct_table[struct_name][item_name] = (offset, item_type.strip())
                else:
                    struct_name = line_split[0]
                    ida_struct_table[struct_name] = {}
    return ida_struct_table


def rm_unused_spaces(content):
    res = content.strip()
    res = re.sub(r'[ ]*\+[ ]*', '+', res)
    res = re.sub(r'[ ]*-[ ]*', '-', res)
    res = re.sub(r'[ ]*\*[ ]*', '*', res)
    res = res.replace('+-', '-')
    return res


def get_ida_ptr_rep_from_item_type(item_type):
    res = None
    if item_type in (('dd', 'dq', 'db', 'dw')):
        suffix = item_type[-1]
        res = BYTE_REP_PTR_MAP[suffix]
    return res


def convert_imm_endh_to_hex(imm):
    tmp = imm.rsplit('h', 1)[0].strip()
    res = hex(int(tmp, 16))
    return res


def normalize_arg_byte_len_rep(arg):
    res = arg
    if arg.endswith(']'):
        b_len_rep = arg.split(' ', 1)[0].strip()
        if b_len_rep in BYTE_LEN_REPS:
            res = re.sub(b_len_rep, BYTE_LEN_REPS[b_len_rep], arg)
    return res


def generate_ida_ptr_rep(name, inst, length):
    word_ptr_rep = None
    if name.startswith('jmp'):
        word_ptr_rep = BYTELEN_REP_MAP[utils.MEM_ADDR_SIZE]
    elif name == 'call':
        word_ptr_rep = BYTELEN_REP_MAP[utils.MEM_ADDR_SIZE]
    elif name in ('mov', 'cmp'):
        if length:
            word_ptr_rep = BYTELEN_REP_MAP[length]
    elif name.startswith(('j')):
        word_ptr_rep = BYTELEN_REP_MAP[utils.MEM_ADDR_SIZE]
    elif name.startswith(('set')):
        word_ptr_rep = 'byte ptr'
    elif name in (('subs', 'movs', 'ucomis')):
        word_ptr_rep = 'dword ptr'
    elif name in (('movdqu', 'movaps', 'movdqa', 'movups')):
        word_ptr_rep = 'xmmword ptr'
    elif name == 'movq' and 'xmm' in inst:
        pass
    elif name == 'movsxd':
        if length in (16, 32):
            word_ptr_rep = BYTELEN_REP_MAP[length]
        else:
            word_ptr_rep = 'dword ptr'
    elif name == 'movss':
        word_ptr_rep = 'dword ptr'
    return word_ptr_rep


def eval_simple_formula(stack, op_stack):
    res = stack[0]
    for idx, op in enumerate(op_stack):
        if op == '+':
            res = res + stack[idx + 1]
        elif op == '-':
            res = res - stack[idx + 1]
    return res


def reconstruct_formula_expr(stack, op_stack, idx_list, imm_val):
    res = ''
    for idx, val in enumerate(stack):
        if idx not in idx_list:
            if idx > 0:
                res += op_stack[idx - 1] + val
            else:
                res += val
    if res:
        res += '+' + hex(imm_val)
    else:
        res = hex(imm_val)
    res = res.replace('+-', '-')
    return res


def reconstruct_formula(stack, op_stack):
    res = ''
    for idx, val in enumerate(stack):
        if idx > 0:
            op = op_stack[idx - 1] 
            res += op
            if op in ('+', '-') and utils.imm_start_pat.match(val):
                res += hex(utils.imm_str_to_int(val))
            else:
                res += val
        else:
            res += val
    res = res.replace('+-', '-')
    return res


def calc_formula_expr(stack, op_stack, content):
    res = content
    imm_item_list = [(idx, utils.imm_str_to_int(val)) for idx, val in enumerate(stack) if utils.imm_pat.match(val) and (idx == 0 or op_stack[idx - 1] in (('+', '-')))]
    idx_list = []
    val_list = []
    oper_list = []
    for idx, val in imm_item_list:
        num_val = val
        if idx > 0:
            op = op_stack[idx - 1]
            if val_list:
                oper_list.append(op)
            else:
                num_val = val if op == '+' else -val
        idx_list.append(idx)
        val_list.append(num_val)
    if len(val_list) > 1:
        imm_val = eval_simple_formula(val_list, oper_list)
        res = reconstruct_formula_expr(stack, op_stack, idx_list, imm_val)
    else:
        res = reconstruct_formula(stack, op_stack)
    return res


def simulate_eval_expr(content):
    stack = []
    op_stack = []
    line = rm_unused_spaces(content)
    line_split = simple_operator_pat.split(line)
    for lsi in line_split:
        lsi = lsi.strip()
        if simple_operator_pat.match(lsi):
            op_stack.append(lsi)
        else:
            val = lsi
            stack.append(val)
    res = calc_formula_expr(stack, op_stack, content)
    return res
