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
import random
import os
import sys
import errno
from typing import List
import logging
import subprocess
from . import lib
from enum import Enum

MAX_LOOP_COUNT = 5

MAX_VISIT_COUNT = 25

MAX_TRACEBACK_COUNT = 50
MAX_INST_ADDR_GAP = 25

INIT_STACK_FRAME_POINTER = 2**48-9
MAX_DEVIATION = 5
SEGMENT_REG_INIT_VAL = 0
CMC_EXEC_RES_COUNT = 4
MAX_STACK_SIZE = 0x4000

MAX_ARGC_NUM = 10
REBUILD_BRANCHES_NUM = 2

INIT_BLOCK_NO = -1
TB_DEFAULT_BLOCK_NO = -2

MEM_ADDR_SIZE = 32

ADDR_SIZE_SP_MAP = {
    16: 'sp',
    32: 'esp',
    64: 'rsp'
}
INIT_STACK_FRAME_POINTER = {
    16: 0xfff0,
    32: 0xffffff00,
    64: 0xffffffffffff0000
}

MIN_STACK_FRAME_POINTER = INIT_STACK_FRAME_POINTER[MEM_ADDR_SIZE] - MAX_STACK_SIZE

HEAP_ADDR_INFO = {
    16: 0x4ff,
    32: 0x8fffff,
    64: 0x10000000
}

MAX_MALLOC_SIZE = 1671
MIN_HEAP_ADDR = HEAP_ADDR_INFO[MEM_ADDR_SIZE]
MAX_HEAP_ADDR = MIN_HEAP_ADDR


ASSEMBLY_FILE_NAME = 'test.s'
PREDEFINED_CONSTRAINT_FILE = 'ext_env.config'

INVALID_SECTION_LABELS = {'_init', '_fini', '__libc_csu_init', '__libc_csu_fini', 'frame_dummy', 'register_tm_clones', 'deregister_tm_clones', '__do_global_dtors_aux'}

PROJECT_DIR = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(os.path.realpath(__file__)))))

LOG_NAMES = ['log', 'output']

logger = logging.getLogger(LOG_NAMES[0])
output_logger = logging.getLogger(LOG_NAMES[1])

def setup_logger(log_name, log_path, verbose, level=logging.INFO):
    file_handler = logging.FileHandler(log_path, mode='w+')
    if log_name == LOG_NAMES[0]:
        global logger
        logger = logging.getLogger(log_name)
        logger.setLevel(level)
        if not verbose:
            logger.propagate = False
        logger.addHandler(file_handler)
    else:
        global output_logger
        output_logger = logging.getLogger(log_name)
        output_logger.setLevel(level)
        if not verbose:
            output_logger.propagate = False
        output_logger.addHandler(file_handler) 
    

def close_logger(log_name):
    if log_name == LOG_NAMES[0]:
        global logger
        logger = logging.getLogger(log_name)
        for handler in logger.handlers:
            handler.close()
            logger.removeHandler(handler)
    else:
        global output_logger
        output_logger = logging.getLogger(log_name)
        for handler in output_logger.handlers:
            handler.close()
            output_logger.removeHandler(handler)


delimits = {'(': ')', '[': ']', '{': '}'}
exec_file_suffix = ['', '.so', '.o', '.os']
float_pat = re.compile('^[0-9.]+$|^-[0-9.]+$')
simple_operator_pat = re.compile(r'(\+|-|\*)')
imm_pat = re.compile('^0x[0-9a-fA-F]+$|^[0-9]+$|^-[0-9]+$|^-0x[0-9a-fA-F]+$')
imm_start_pat = re.compile('^0x[0-9a-fA-F]+|^[0-9]+|^-[0-9]+|^-0x[0-9a-fA-F]+')
imm_pat_wo_prefix = re.compile('^[0-9a-fA-F]+$|^-[0-9a-fA-F]+$')

MEM_DATA_SEC_SUFFIX = 'mem@'
LOG_UNREACHABLE_INDICATOR = 'Unreachable instructions:'
SOUNDNESS_EXCEPTION_INDICATOR = 'ambiguous operand size'

OPPOSITE_FLAG_MAP = {
    'b': 'ae',
    'be': 'a',
    'l': 'ge',
    'le': 'g'
}

def imm_str_to_int(imm_str):
    res = 0
    if imm_str.startswith(('0x', '-0x')):
        res = int(imm_str, 16)
    elif re.search(r'[a-f]+', imm_str):
        res = int(imm_str, 16)
    elif imm_str.endswith('h'):
        res = int(imm_str.rsplit('h', 1)[0], 16)
    else:
        res = int(imm_str)
    return res


def convert_imm_endh_to_hex(imm):
    tmp = imm.rsplit('h', 1)[0].strip()
    res = hex(int(tmp, 16))
    return res


def make_dir(path):
    try:
        os.makedirs(path, exist_ok=True)
    except OSError as exc:
        if exc.errno == errno.EEXIST and os.path.isdir(path):
            pass
        else: raise

def sign_extend(value, bits):
    sign_bit = 1 << (bits - 1)
    return (value & (sign_bit - 1)) - (value & sign_bit)

# input: [1, 2, 3]  [1, 2, 4]
# output: [3]
def diff_list(l1, l2):
    l1_minus_l2 = list(set(l1) - set(l2))
    l2_minus_l1 = list(set(l2) - set(l1))
    l1_minus_l2.extend(l2_minus_l1)
    return l1_minus_l2


def extract_content(expr: str, left_delimit='(') -> str:
    right_delimit = delimits[left_delimit]
    return expr.split(left_delimit, 1)[1].rsplit(right_delimit, 1)[0].strip()


def subtract_list(l1, l2):
    l3 = [elem for elem in l1 if elem not in l2]
    return l3


def flatten(l):
    r"""Flatten a list of list to a list
        Args:
            l (List[List[T]]): a list whose elements are also list
        """
    return [a for sl in l for a in sl]


def has_dup(l):
    r"""Check whether there are duplicated elements in a list
        Args:
            l (List[T]): a list who might have duplicated elements
        """
    return len(l) != len(set(l))


def check_executable_file(file_path):
    cmd = 'file ' + file_path + ' | grep "ELF 64-bit LSB shared object"'
    out = execute_command(cmd)
    if out.strip():
        return True
    else:
        return False

def get_exec_path(file_dir, file_name, disasm_type='objdump'):
    exec_path = None
    exec_file_dir = file_dir.replace('-'+disasm_type, '-build')
    for suffix in exec_file_suffix:
        curr_file_name = file_name.replace('.'+disasm_type, suffix)
        exec_path = os.path.join(exec_file_dir, curr_file_name)
        if os.path.exists(exec_path) and check_executable_file(exec_path):
            return exec_path
    return exec_path

def get_exec_path_from_log(file_dir, file_name, disasm_type='objdump'):
    exec_path = None
    exec_file_dir = file_dir.replace('-'+disasm_type, '-build')
    for suffix in exec_file_suffix:
        curr_file_name = file_name.replace('.log', suffix)
        exec_path = os.path.join(exec_file_dir, curr_file_name)
        if os.path.exists(exec_path) and check_executable_file(exec_path):
            return exec_path
    return exec_path

def get_file_dir(file_path):
    file_dir = file_path.rsplit('/', 1)[0]
    return file_dir


def get_file_name(path):
    file_name = path.rsplit('/', 1)[1]
    return file_name


# Extract the contents inside symmetric parenthese inside the string
# input: '(123) 45 (678(42) 235) 56', '(', ')'
# output: ['(123)', '(678(42) 235)']
def extract_bk_content(args:str, left = '(', right = ')')->List[str]:
    result = []
    to_continue = False
    curr = ''
    bk_count = 0
    for c in args:
        if c == left:
            curr += left
            bk_count += 1
            to_continue = True
        elif c == right:
            bk_count -= 1
            curr += right
            if bk_count == 0:
                to_continue = False
                curr = curr.strip()
                if curr != '':
                    result.append(curr)
                curr = ''
                bk_count = 0
        else:
            if to_continue:
                curr += c
    return result


# input: '(123) 45 (678(42) 235) 56 [78 9]', ' ', ['(', '['], [')', ']']
# output: ['(123)', '45', '(678(42) 235)', '56', '[78 9]']
def split_sep_bks(data, sep, left = ['(', '[', '{'], right = [')', ']', '}']):
    sep_first = sep[0]
    sep_len = len(sep)
    result = []
    curr = ''
    to_continue = False
    idx = 0
    length = len(data)
    bk_len = len(left)
    bk_count = [0] * bk_len
    while idx < length:
        c = data[idx]
        if c in left:
            c_idx = left.index(c)
            bk_count[c_idx] += 1
            curr += c
            to_continue = True
            idx += 1
        elif c in right:
            c_idx = right.index(c)
            curr += c
            bk_count[c_idx] -= 1
            if all(elem == 0 for elem in bk_count):
                to_continue = False
            idx += 1
        elif c == sep_first and len(data[idx:]) >= sep_len and data[idx: idx + sep_len] == sep:
            if to_continue:
                curr += c
                idx += 1
            else:
                curr = curr.strip()
                if curr != '':
                    result.append(curr)
                curr = ''
                idx += sep_len
        else:
            curr += c
            idx += 1
    result.append(curr.strip())
    return result


# Extract the arguments of the first element from a tuple represented as a string
# input: '(cons(x, xs), cons(y, ys))'
# output: ['x', 'xs']
def extract_tuple_first_arg(t: str) -> List[str]:
    result = []
    first = ''
    if t:
        if t.startswith('('):
            ts = split_arg_list(t)
            first = ts[0].strip()
        else:
            first = t.strip()
    if first.endswith(')'):
        args = extract_content(first)
        result = split_sep_bks(args, ',')
    return result


# Remove the first element from a tuple represented as a string
# input: '(cons(x, xs), cons(y, ys))'
# output: 'cons(y, ys)'
def remove_tuple_first_element(t: str) -> str:
    result = ''
    if t.startswith('('):
        ts = split_sep_bks(extract_content(t), ',')
        result = '(' + ','.join(ts[1:]) + ')'
    return result


def generate_new_variable(tup_idx: int, arg_idx: int) -> str:
    tup_str = 'v_' + chr(ord('a') + tup_idx)
    result = tup_str + ('' if arg_idx == 0 else str(arg_idx))
    return result


def replace_expr_variable(expr: str, ov: str, nv: str) -> str:
    reg = '(?<=\W)' + ov + '(?=\W)'
    result = re.sub(reg, nv, expr)
    return result


# Split a arguments representation
# '(T,list[T])'
# ['T', 'list[T]']
def split_arg_list(expr: str, delimit='(') -> List[str]:
    if expr.startswith(delimit):
        expr = extract_content(expr, delimit)
    return split_sep_bks(expr, ',')


# Indent multiple lines
def block_indent(expr: str, indent_size='4') -> str:
    new_indent = '\n' + ' ' * indent_size
    return re.sub('\n', new_indent, expr)


# Replace multiple variables
def replace_multiple(expr, os, ns):
    result = expr
    n = len(os)
    for i in range(n):
        o = os[i]
        n = ns[i]
        result = re.sub(o, n, result)
    return result


def execute_command(cmd):
    res = ''
    try:
        out = subprocess.check_output(cmd, shell=True ,stderr=subprocess.STDOUT)
        res = out.decode("utf-8").strip()
    except subprocess.CalledProcessError as exc:
        pass
    else:
        pass
    return res


def write_file(file_path, data):
    with open(file_path, 'w+') as f:
        f.write(data)

def to_absolute_path(path, dir_path=''):
    if path.startswith('..'):
        path = re.sub('\.\./', os.path.dirname(dir_path) + '/', path)
    elif path.startswith('./'):
        path = re.sub('\./', dir_path + '/', path)
    elif path.startswith('~/'):
        path = os.path.expanduser(path)
    elif not path.startswith('/'):
        path = os.path.join(dir_path, path)
    return path


def convert_dot_to_png(file_path):
    cmd = 'dot -Tpng ' + file_path + '.dot > ' + file_path + '.png'
    execute_command(cmd)


def replace_dot_in_func_name(name):
    res = name.replace('.', '_dot_')
    res = res.replace('@', '_at_')
    return res


def norm_dot_pp_info(val):
    res = val
    if val.startswith('[') and val.endswith(']'):
        res = val.replace('[', '\\[').replace(']', '\\]')
    return res

def bytes_to_int(bytes):
    # logger.debug(bytes)
    res = ''
    for bs in bytes:
        n = '{0:02x}'.format(bs)
        res += n
    return int(res, 16)


def bytes_to_hex(bytes):
    res = ''
    for bs in bytes:
        n = '{0:02x}'.format(bs)
        res += n
    return res


def dump_str_to_file(content, file_path):
    with open(file_path, 'w+') as f:
        f.write(content)
        f.write('\n')


def generate_inst_bin(line, file_handler, syntax='intel'):
    res = ''
    try:
        line_str = '.intel_syntax noprefix\n' + line
        if syntax == 'att':
            line_str = '.att_syntax noprefix\n' + line
        dump_str_to_file(line_str.strip(), ASSEMBLY_FILE_NAME)
        cmd = 'gcc -c ' + ASSEMBLY_FILE_NAME + ' -o test.o'
        _ = execute_command(cmd)
        cmd = 'readelf -x .text test.o'
        out = execute_command(cmd)
        out_split = out.split('\n')
        for out_elem in out_split:
            if out_elem.startswith('  0x00'):
                res = ''.join(out_elem.strip().split('    ')[0].split(' ')[1:])
                break
    except:
        print('\'' + line + '\' is not a valid instruction for gcc (' + syntax + '-syntax format)')
    return res

    
def get_bytes_len(bytes_rep):
    return len(bytes_rep) // 2


def remove_multiple_spaces(line):
    return ' '.join(line.split())


def str_to_bytes(line):
    line = line.replace(' ', '')
    return int(line, 16).to_bytes(len(line)//2, byteorder='big')


def id_op(arg):
    return arg


def get_bin_rep(s):
    return str(s) if s<=1 else get_bin_rep(s>>1) + str(s&1)


def get_sub_bits(num, start_idx, end_idx):
    bin_rep = get_bin_rep(num)
    bin_rep = bin_rep[start_idx:end_idx]
    res = int(bin_rep, 2)
    return res


def generate_sym_expr(num):
    ''' Automatically generate a string using a given number '''
    curr = num % 26
    res = chr(ord('a') + curr)
    while num > 25:
        num = num // 26
        curr = num % 26
        res += chr(ord('a') + curr)
    return res


def check_branch_inst(inst):
    inst_name = inst.strip().split(' ', 1)[0]
    return inst_name in lib.JMP_INST or inst.endswith(' ret') or inst.startswith('ret')

def check_branch_inst_wo_call(inst):
    inst_name = inst.strip().split(' ', 1)[0]
    return inst_name in lib.JMP_INST_WITHOUT_CALL or inst.endswith(' ret') or inst.startswith('ret ')

def check_not_single_branch_inst(inst):
    inst_name = inst.strip().split(' ', 1)[0]
    return inst_name in lib.CONDITIONAL_JMP_INST


def check_jmp_with_address(line):
    inst_name = line.strip().split(' ', 1)[0]
    return inst_name in lib.JMP_INST_WITH_ADDRESS


def check_jmp_with_jump_instr(line):
    inst_name = line.strip().split(' ', 1)[0]
    return inst_name in lib.JMP_INST_WITH_JUMP


def get_mem_sym_length(sym_name):
    res = 128
    if sym_name.startswith('qword '): res = 64
    elif sym_name.startswith('dword '): res = 32
    elif sym_name.startswith('word '): res = 16
    elif sym_name.startswith('byte '):res = 8
    return res


def rm_unused_spaces(content):
    res = content.strip()
    res = re.sub(r'[ ]*\+[ ]*', '+', res)
    res = re.sub(r'[ ]*-[ ]*', '-', res)
    res = re.sub(r'[ ]*\*[ ]*', '*', res)
    res = res.replace('+-', '-')
    return res
    

def init_ida_struct_info():
    ida_struct_table = {}
    ida_info_path = os.path.join(PROJECT_DIR, 'ida_struct.info')
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


# def get_sym_length(sym_name, length=MEM_ADDR_SIZE):
#     res = length
#     if sym_name in lib.REG64_NAMES: res = 64
#     elif sym_name in lib.REG_INFO_DICT:
#         _, _, res = lib.REG_INFO_DICT[sym_name]
#     elif sym_name.endswith(']') or ' ptr ' in sym_name:
#         res = get_mem_sym_length(sym_name)
#     elif ':' in sym_name:     #rax:rdx
#         regs = sym_name.split(':')
#         left_len = get_sym_length(regs[0])
#         right_len = get_sym_length(regs[1])
#         res = left_len + right_len
#     return res


def get_sym_length(sym_name, length=MEM_ADDR_SIZE):
    res = length
    if sym_name in lib.REG64_NAMES: res = 64
    elif sym_name in lib.REG_INFO_DICT:
        _, _, res = lib.REG_INFO_DICT[sym_name]
    elif sym_name.endswith(']') or ' ptr ' in sym_name:
        res = get_mem_sym_length(sym_name)
    elif ':' in sym_name:     #rax:rdx
        if 's:' not in sym_name:
            regs = sym_name.split(':')
            left_len = get_sym_length(regs[0])
            right_len = get_sym_length(regs[1])
            res = left_len + right_len
        else:
            new_sym = sym_name.split(':', 1)[1].strip()
            if new_sym:
                res = get_sym_length(new_sym)
    return res

def get_signed_integer(num, bits_len):
    mask = (2 ** bits_len) - 1
    if num & (1 << (bits_len - 1)):
        return num | ~mask
    else:
        return num & mask


def extract_inst_args(inst_split):
    inst_args = []
    if len(inst_split) > 1:
        inst_args = split_sep_bks(inst_split[1].strip(), ',', ['(', '{', '[', '<'], [')', '}', ']', '>'])
        inst_args = list(map(lambda x: x.strip(), inst_args))
    return inst_args


def parse_inst_args(inst_split):
    inst_args = []
    if len(inst_split) > 1:
        inst_args = inst_split[1].strip().split(',')
        inst_args = list(map(lambda x: x.strip(), inst_args))
    return inst_args


def read_glibc_elf_info(file_path):
    address_sym_table = {}
    with open(file_path, 'r') as f:
        lines = f.readlines()
        for line in lines:
            line_split = line.strip().split('->')
            address = imm_str_to_int(line_split[0].strip())
            syms = line_split[1].split('[', 1)[1].rsplit(']', 1)[0].strip()
            sym_list = syms.split(', ')
            sym_list = [sym.split('\'', 1)[1].rsplit('\'', 1)[0].strip() for sym in sym_list]
            address_sym_table[address] = sym_list
    return address_sym_table


#   line: '[ 1] .interp           PROGBITS         0000000000000238  00000238'
def read_glibc_data_base_addr(src_bin_path):
    section_headers = execute_command('readelf -S ' + src_bin_path)
    lines = section_headers.split('\n')
    data_base_addr = None
    for line in lines:
        if '.data' in line:
            line_split = remove_multiple_spaces(line.strip()).split(' ')
            section_name = line_split[-4].strip()
            if section_name == '.data':
                section_address = int(line_split[-2], 16)
                section_offset = int(line_split[-1], 16)
                data_base_addr = section_address - section_offset
    return data_base_addr



def insert_search(sorted_list, target):
    res = None
    length = len(sorted_list)
    left = 0
    right = length - 1
    while left <= right:
        mid = left + ((target- sorted_list[left]) * (right - left))//(sorted_list[right] - sorted_list[left])
        if mid < 0 or mid >= length: break
        curr = sorted_list[mid]
        if curr == target:
            res = mid
            break
        elif target < curr:
            right = mid - 1
        else:
            left = mid + 1
    return res


def get_executable_files(file_path):
    cmd = 'ls -d -1 "' + file_path + '/"* | xargs file | grep -e "ELF 64-bit LSB shared object" -e " PE32 executable "'
    # cmd = 'ls -d -1 "' + file_path + '/"* | xargs file | grep " PE32 executable "'
    out = execute_command(cmd)
    out_split = out.split('\n')
    files = []
    for file_info in out_split:
        file_path = file_info.split(':', 1)[0].strip()
        if file_path.strip():
            files.append(file_path)
    return files


def u_hex(num):
    res = hex(num)
    res = res.split('0x', 1)[1]
    return res


