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

# python -m src.check.check_reachability -l benchmark/pe_benchmarks -d benchmark/pe_benchmarks -f HOSTNAME.EXE

import os
import re
import argparse

from ..common import lib
from ..common import utils

address_inst_pattern = re.compile('^[.a-zA-Z]+:[0-9a-zA-Z]+[ ]{17}[a-zA-Z]')

imm_pat = re.compile('^0x[0-9a-fA-F]+$|^[0-9]+$|^-[0-9]+$|^-0x[0-9a-fA-F]+$|^[0-9a-fA-F]+$|^-[0-9a-fA-F]+$')

variable_expr_pat = re.compile(r'^[.a-zA-Z_0-9]+:[0-9a-zA-Z]{16} [a-zA-Z0-9_]+')
non_inst_prefix = ('dd ', 'dw', 'db', 'text ', 'align', 'assume', 'public')


def parse_idapro_line(line):
    address, inst = None, None
    if line:
        line = utils.remove_multiple_spaces(line)
        line_split0 = line.split(';', 1)[0]
        line_split = line_split0.split(' ', 1)
        if len(line_split) == 2:
            address_str = line_split[0].rsplit(':', 1)[1].strip()
            address = int(address_str, 16)
            inst = line_split[1].strip()
    return address, inst


def is_located_at_code_segments(line):
    return line.startswith(lib.CODE_SEGMENTS)


def div_block(angr_path):
    block_range_map = {}
    with open(angr_path, 'r') as f:
        in_block = False
        start_addr = None
        last_addr = None
        lines = f.readlines()
        for line in lines:
            line = line.strip()
            if in_block:
                if line:
                    address, inst = parse_angr_line(line)
                    if inst:
                        last_addr = address
                else:
                    in_block = False
                    block_range_map[start_addr] = last_addr
            else:
                if line:
                    address, inst = parse_angr_line(line)
                    if inst:
                        block_range_map[address] = None
                        in_block = True
                        start_addr = address
                        last_addr = address
        block_range_map[start_addr] = last_addr
    inst_addresses = sorted(list(block_range_map.keys()))
    # print(inst_addresses)
    return block_range_map, inst_addresses


# line: '0x5f0:	cmp	byte ptr [rip + 0x200a19], 0'
def parse_angr_line(line):
    line_split = utils.remove_multiple_spaces(line).split(' ', 1)
    address = int(line_split[0].split(':')[0], 16)
    inst = line_split[1]
    return address, inst


def collect_valid_addr_set(idapro_path):
    address_set = set([])
    invalid_address_set = set([])
    block_start_addrs = []
    with open(idapro_path, 'r') as f:
        in_block = False
        lines = f.readlines()
        for line in lines:
            line = line.strip()
            if line:
                if in_block:
                    if variable_expr_pat.search(line):
                        in_block = False
                    elif is_located_at_code_segments(line):
                        if address_inst_pattern.search(line):
                            address, inst = parse_idapro_line(line)
                            if inst and not inst.startswith(non_inst_prefix):
                                if address not in invalid_address_set:
                                    address_set.add(address)
                            else:
                                in_block = False
                                invalid_address_set.add(address)
                    else:
                        in_block = False
                else:
                    if variable_expr_pat.search(line):
                        pass
                    elif is_located_at_code_segments(line):
                        if address_inst_pattern.search(line):
                            address, inst = parse_idapro_line(line)
                            if inst and not inst.startswith(non_inst_prefix):
                                if address not in invalid_address_set:
                                    in_block = True
                                    block_start_addrs.append(address)
                                    address_set.add(address)
                            else:
                                invalid_address_set.add(address)
    block_start_addrs.sort()
    return address_set, block_start_addrs


def find_start_addr(inst_addresses, address):
    for idx in range(len(inst_addresses) - 1):
        curr_addr = inst_addresses[idx]
        next_addr = inst_addresses[idx + 1]
        if address >= curr_addr and address < next_addr:
            return curr_addr
    return None

def check(log_path, angr_path, idapro_path):
    # block_range_map, inst_addresses = div_block(angr_path)
    address_set, block_start_addrs = collect_valid_addr_set(idapro_path)
    with open(log_path, 'r') as f:
        unreach = False
        count = 0
        blk_count = 0
        s_addr = None
        address = None
        lines = f.readlines()
        for line in lines:
            line = line.strip()
            if line:
                if unreach:
                    address = line.split(':', 1)[0].strip()
                    address = int(address, 16)
                    if address in address_set:
                        start_addr = find_start_addr(block_start_addrs, address)
                        if s_addr:
                            if start_addr != s_addr:
                                print('\n')
                                print(hex(address))
                                s_addr = start_addr
                                blk_count += 1
                            else:
                                print(hex(address))
                        else:
                            s_addr = start_addr
                            print(hex(address))
                        count += 1
                elif line.startswith(utils.LOG_UNREACHABLE_INDICATOR):
                        unreach = True
        if address:
            print(hex(address))
        blk_count += 1
        print('\n')
        print(count)
        print(blk_count)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description='Concolic model checker results checking')
    parser.add_argument('-t', '--disasm_type', default='angr', type=str, help='Disassembler type')
    parser.add_argument('-f', '--file_name', type=str, help='Benchmark file name')
    parser.add_argument('-d', '--disasm_dir', default='benchmark/coreutils-build', type=str, help='Benchmark folder name')
    parser.add_argument('-l', '--log_dir', default='benchmark/coreutils-objdump', type=str, help='Disassembled folder name')
    args = parser.parse_args()
    disasm_type = args.disasm_type
    log_dir = args.log_dir
    log_path = os.path.join(utils.PROJECT_DIR, os.path.join(log_dir, args.file_name + '.log'))
    disasm_path = os.path.join(utils.PROJECT_DIR, os.path.join(args.disasm_dir, args.file_name))
    check(log_path, disasm_path + '.' + disasm_type, disasm_path + '.idapro')
