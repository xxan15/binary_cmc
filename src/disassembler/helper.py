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
import sys
import angr
import r2pipe

from ..common import lib
from ..common import utils


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


remote_addr_pat = re.compile('0x2[0-9a-fA-F]{5}')


def disassemble_to_asm(exec_path, disasm_path, disasm_type='objdump'):
    if os.path.exists(disasm_path): return
    elif disasm_type == 'radare2':
        disassemble_radare2(exec_path, disasm_path)
    elif disasm_type == 'objdump':
        cmd = 'objdump -M intel -d ' + exec_path + ' > ' + disasm_path
        utils.execute_command(cmd)
    elif disasm_type == 'angr':
        disassemble_angr(exec_path, disasm_path)
    else:
        raise Exception('The assembly file has not been generated')


def disassemble_angr(exec_path, asm_path):
    proj = angr.Project(exec_path, auto_load_libs=False, load_options={'main_opts': {'base_addr': 0x000000}})
    cfg = proj.analyses.CFGFast()
    nodes = cfg.graph.nodes()
    sys.stdout = open(asm_path, 'w+')
    for node in nodes:
        if node and node.block:
            node.block.pp()
        print('\n')
    sys.stdout.close()


def disassemble_radare2(exec_path, asm_path):
    res = ''
    r = r2pipe.open(exec_path)
    r.cmd('e asm.lines=false')
    r.cmd('e asm.syntax = intel')
    s_info = r.cmd('iS')
    sec_size_table = parse_r2_section_info(s_info)
    for sec_name in (('.plt', '.plt.got', '.text')):
        if sec_name in sec_size_table:
            r.cmd('s section.' + sec_name)
            res += r.cmd('pD ' + str(sec_size_table[sec_name]))
    with open(asm_path, 'w+') as f:
        f.write(res)

    
# [Sections]
# Nm Paddr       Size Vaddr      Memsz Perms Name
# ...
# 14 0x00001510 13070 0x00001510 13070 -r-x .text
# 15 0x00004820     9 0x00004820     9 -r-x .fini
def parse_r2_section_info(section_info):
    prev_name = ''
    prev_address = 0
    lines = section_info.split('\n')
    sec_size_table = {}
    sec_start = False
    for line in lines:
        line_split = utils.remove_multiple_spaces(line).split(' ')
        if len(line_split) == 7:
            if utils.imm_pat.match(line_split[1]):
                address = utils.imm_str_to_int(line_split[1])
                if sec_start:
                    sec_size_table[prev_name] = address - prev_address
                else:
                    sec_start = True
                prev_address = address
                prev_name = line_split[-1]
    return sec_size_table


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
    elif disassembler == 'radare2':
        result = re.match(r'^[ ]+;-- [0-9a-zA-Z._]+:', line)
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
                res = '[rip+' + str(to_hex(relative_address, 64)) + ']'
            if arg.startswith(('qword', 'dword', 'word', 'byte', 'tbyte', 'xmmword')):
                res = arg_split[0] + res
    elif re.match(r'^0x[0-9a-f]+$|^-0x[0-9a-f]+$', arg):
        res = hex(utils.imm_str_to_int(arg))
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


def normalize_radare2_arg(inst_name, arg):
    res = arg
    if inst_name.startswith(('cmpsb', 'scasb')) and ']' in arg:
        res = arg.rsplit(' ', 1)[1].strip()
    elif arg.endswith(']') and ' ptr ' not in arg:
        b_len_rep = arg.split(' ', 1)[0].strip()
        if b_len_rep in BYTE_LEN_REPS:
            res = re.sub(b_len_rep, BYTE_LEN_REPS[b_len_rep] + ' ptr', arg)
    return res


def retrieve_bytelen_rep(name, args):
    word_ptr_rep = None
    if len(args) == 1:
        if args[0].endswith(']'):
            word_ptr_rep = 'qword ptr'
    elif name in (('movsx', 'movzx')):
        word_ptr_rep = 'byte ptr'
        # if args[0] in lib.REG_INFO_DICT:
        #     word_len = lib.REG_INFO_DICT[args[0]][2]
        #     if word_len == 16: word_ptr_rep = 'byte ptr'
        #     else:
        #         word_ptr_rep = 'word ptr'
        # elif args[0] in lib.REG64_NAMES:
        #     word_ptr_rep = 'word ptr'
    elif name in (('movsd', 'movsb', 'movsxd')):
        word_ptr_rep = BYTE_REP_PTR_MAP[name[-1]]
    elif utils.check_branch_inst(name):
        word_ptr_rep = 'qword ptr'
    elif name != 'lea':
        for arg in args:
            if arg in lib.REG_INFO_DICT:
                word_len = lib.REG_INFO_DICT[arg][2]
                word_ptr_rep = BYTELEN_REP_MAP[word_len]
                break
            elif arg in lib.REG64_NAMES:
                word_ptr_rep = BYTELEN_REP_MAP[64]
                break
    return word_ptr_rep


def add_jump_address_wordptr_rep(arg):
    res = arg
    if arg.endswith(']'):
        res = 'qword ptr ' + arg
    return res


# input1: 'mov    rax,QWORD PTR [rip+0x200a5a] '
# output1: 'mov    rax,qword ptr [rip+0x200a5a] '
def norm_ptr_rep(line):
    res = line
    if ' PTR ' in line or ' ptr ' in line:
        for byte_len_rep in BYTE_LEN_REPS:
            res = re.sub(byte_len_rep + ' PTR ', byte_len_rep.lower() + ' ptr ', res)
    else:
        for d_type in BYTE_LEN_REPS:
            d_type_rep = d_type + ' '
            d_type_lower_rep = d_type.lower() + ' '
            if d_type_rep in line:
                res = re.sub(d_type_rep, d_type_lower_rep + ' ptr ', res)
            elif ',' + d_type_lower_rep in line or ' ' + d_type_lower_rep in line or '\t' + d_type_lower_rep in line:
                res = re.sub(d_type_lower_rep, d_type_lower_rep + ' ptr ', res)
    return res


