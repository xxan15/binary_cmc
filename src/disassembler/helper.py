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

from ..common import utils


remote_addr_pat = re.compile('0x2[0-9a-fA-F]{5}')

def disassemble_to_asm(exec_path, disasm_path, disasm_type='objdump'):
    if os.path.exists(disasm_path): return
    if disasm_type == 'objdump':
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

