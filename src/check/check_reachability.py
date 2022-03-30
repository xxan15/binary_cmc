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

# python -m src.check.check_reachability -l benchmark/pe_benchmark -d benchmark/pe_benchmark -f HOSTNAME.EXE
# python -m src.check.check_reachability -e benchmark/coreutils-5.3.0-bin/bin -l benchmark/coreutils-5.3.0-angr -i benchmark/coreutils-5.3.0-idapro -f basename.exe

import os
import re
import argparse


from ..common import lib
from ..common import utils
from ..binary.binary_info import Binary_Info
from ..disassembler.disasm_angr import Disasm_Angr
from ..disassembler.disasm_idapro import Disasm_IDAPro
from .construct_graph import Construct_Graph

target_dir = os.path.join(utils.PROJECT_DIR, 'temp')

address_inst_pattern = re.compile('^[.a-zA-Z]+:[0-9a-zA-Z]+[ ]{17}[a-zA-Z]')

imm_pat = re.compile('^0x[0-9a-fA-F]+$|^[0-9]+$|^-[0-9]+$|^-0x[0-9a-fA-F]+$|^[0-9a-fA-F]+$|^-[0-9a-fA-F]+$')

variable_expr_pat = re.compile(r'^[.a-zA-Z_0-9]+:[0-9a-zA-Z]{16} [a-zA-Z0-9_]+')

non_inst_prefix = ('dd ', 'dw', 'db', 'text ', 'align', 'assume', 'public', 'start', 'type')


def is_located_at_code_segments(line):
    return line.startswith(lib.CODE_SEGMENTS)


def append_all_addresses(start_address, end_address, inst_addresses, address_inst_map, graph):
    # res = ''
    cnt = 0
    if start_address in inst_addresses:
        s_idx = inst_addresses.index(start_address)
        if end_address in inst_addresses:
            e_idx = inst_addresses.index(end_address)
            for idx in range(s_idx, e_idx + 1):
                address = inst_addresses[idx]
                inst = address_inst_map[address]
                if not (inst.startswith('nop ') or inst == 'nop'):
                    cnt += 1
                    # res += utils.u_hex(address) + ': ' + inst + '\n'
    # res += '\n'
    return cnt


def divide_to_block(new_content):
    start_address_list = []
    end_address_list = []
    _exists = False
    lines = new_content.split('\n')
    for line in lines:
        if line:
            address_str, _ = line.strip().split(':', 1)
            address = int(address_str, 16)
            if not _exists:
                start_address_list.append(address)
                _exists = True
        else:
            if _exists:
                end_address_list.append(address)
            _exists = False
    return start_address_list, end_address_list


def count_implicit_called_functions(new_content, unreach_addresses, graph):
    global cond_jump_unreached_cnt, c_blk_cnt, implicit_called_cnt, i_blk_cnt, unreached_entries_cnt, u_blk_cnt
    start_address_list, end_address_list = divide_to_block(new_content)
    inst_addresses = graph.inst_addresses
    address_inst_map = graph.address_inst_map
    address_entries_map = graph.address_entries_map
    reached_entry = False
    for start_address, end_address in zip(start_address_list, end_address_list):
        if start_address in graph.block_start_addrs:
            if start_address in address_entries_map:
                if len(address_entries_map[start_address]) > 0:
                    for entry_address in address_entries_map[start_address]:
                        # If the entry point to the address is reachable
                        if entry_address not in unreach_addresses:
                            reached_entry = True
                            cnt = append_all_addresses(start_address, end_address, inst_addresses, address_inst_map, graph)
                            cond_jump_unreached_cnt += cnt
                            c_blk_cnt += 1
                            break
                    if not reached_entry:
                        cnt = append_all_addresses(start_address, end_address, inst_addresses, address_inst_map, graph)
                        unreached_entries_cnt += cnt
                        u_blk_cnt += 1
            else:
                cnt = append_all_addresses(start_address, end_address, inst_addresses, address_inst_map, graph)
                implicit_called_cnt += cnt
                i_blk_cnt += 1
        else:
            cnt = append_all_addresses(start_address, end_address, inst_addresses, address_inst_map, graph)
            cond_jump_unreached_cnt += cnt
            c_blk_cnt += 1
    

def not_continuous(prev_address, address, graph):
    if prev_address:
        if prev_address in graph.inst_addresses:
            p_idx = graph.inst_addresses.index(prev_address)
            if p_idx + 1 < len(graph.inst_addresses):
                if graph.inst_addresses[p_idx + 1] != address:
                    return True
            else:
                return True
        else:
            return False
    return False


# Remove the real unreachable instructions from the results
def remove_unreachable_inst(new_log_path, graph):
    inst_addresses = graph.inst_addresses
    block_start_addrs = graph.block_start_addrs
    res = ''
    unreach_addresses = []
    count = 0
    blk_count = 0
    with open(new_log_path, 'r') as f:
        unreach = False
        s_addr = None
        address = None
        lines = f.readlines()
        for line in lines:
            line = line.strip()
            if line:
                # We read all the unreached instructions information from the .log file
                if unreach:
                    address = line.split(':', 1)[0].strip()
                    address = int(address, 16)
                    if address in inst_addresses:
                        start_addr = find_start_addr(block_start_addrs, address)
                        # If we already have the starting address of a block
                        if s_addr:
                            if start_addr != s_addr:
                                res += '\n' + line + '\n'
                                unreach_addresses.append(address)
                                s_addr = start_addr
                                blk_count += 1
                            else:
                                res += line + '\n'
                                unreach_addresses.append(address)
                        else:
                            # Set a new starting address for a block
                            s_addr = start_addr
                            res += line + '\n'
                            unreach_addresses.append(address)
                        count += 1
                elif line.startswith(utils.LOG_UNREACHABLE_INDICATOR):
                    unreach = True
        if address:
            unreach_addresses.append(address)
            res += line + '\n'
        blk_count += 1
    with open(new_log_path, 'w+') as f:
        f.write(res)
    return res, unreach_addresses, count, blk_count


def normalize_unreachable(new_log_path, graph):
    # print(graph.unexplored_address_list)
    new_content, unreach_addresses, unreached_count, blk_count = remove_unreachable_inst(new_log_path, graph)
    # print(new_content)
    count_implicit_called_functions(new_content, unreach_addresses, graph)
    # print(new_content)
    # with open(new_log_path, 'w+') as f:
    #     f.write(new_content)
    return unreached_count, blk_count


def read_parameters(output_path):
    res_list = []
    with open(output_path, 'r') as f:
        lines = f.readlines()
        for line in lines:
            line = line.strip()
            if line:
                if '# of reached instructions' in line:
                    reached_cnt = int(line.rsplit(' ', 1)[1])
                elif '# of paths' in line:
                    path_cnt = int(line.rsplit(' ', 1)[1])
                elif '# of unsound paths' in line:
                    neg_path_cnt = int(line.rsplit(' ', 1)[1])
                elif '# of unresolved indirects' in line:
                    indirects_cnt = int(line.rsplit(' ', 1)[1])
    res_list.append(reached_cnt)
    res_list.append(path_cnt)
    res_list.append(neg_path_cnt)
    res_list.append(indirects_cnt)
    return res_list


def neat_main(graph, new_log_path, output_path):
    global cond_jump_unreached_cnt, c_blk_cnt, implicit_called_cnt, i_blk_cnt, unreached_entries_cnt, u_blk_cnt
    cond_jump_unreached_cnt, implicit_called_cnt, unreached_entries_cnt = 0, 0, 0
    c_blk_cnt, i_blk_cnt, u_blk_cnt = 0, 0, 0
    unreached_count, blk_count = normalize_unreachable(new_log_path, graph)
    para_list = read_parameters(output_path)
    para_list.append(unreached_count)
    para_list.append(blk_count)
    para_list.append(cond_jump_unreached_cnt)
    para_list.append(c_blk_cnt)
    para_list.append(implicit_called_cnt)
    para_list.append(i_blk_cnt)
    para_list.append(unreached_entries_cnt)
    para_list.append(u_blk_cnt)
    return para_list


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


def collect_valid_addr_set(idapro_path):
    address_set = set([])
    # invalid_address_set = set([])
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
                                # if address not in invalid_address_set:
                                address_set.add(address)
                            else:
                                in_block = False
                                # invalid_address_set.add(address)
                        else:
                            in_block = False
                    else:
                        in_block = False
                else:
                    if variable_expr_pat.search(line):
                        pass
                    elif is_located_at_code_segments(line):
                        if address_inst_pattern.search(line):
                            address, inst = parse_idapro_line(line)
                            # print(hex(address) + ': ' + inst)
                            if inst and not inst.startswith(non_inst_prefix):
                                # if address not in invalid_address_set:
                                in_block = True
                                block_start_addrs.append(address)
                                address_set.add(address)
                            # else:
                            #     invalid_address_set.add(address)
    block_start_addrs.sort()
    inst_addresses = []
    for address in address_set:
        inst_addresses.append(address)
    inst_addresses.sort()
    return inst_addresses, block_start_addrs


def find_start_addr(inst_addresses, address):
    # print(inst_addresses)
    for idx in range(len(inst_addresses) - 1):
        curr_addr = inst_addresses[idx]
        next_addr = inst_addresses[idx + 1]
        if address >= curr_addr and address < next_addr:
            return curr_addr
    return None

# Collect all the addresses for the unreached instructions
def collect_unreached_addrs(log_path, inst_addresses):
    unexplored_address_list = []
    with open(log_path, 'r') as f:
        unreach = False
        address = None
        lines = f.readlines()
        for line in lines:
            line = line.strip()
            if line:
                if unreach:
                    address = line.split(':', 1)[0].strip()
                    address = int(address, 16)
                    if address in inst_addresses:
                        unexplored_address_list.append(address)
                elif line.startswith(utils.LOG_UNREACHABLE_INDICATOR):
                        unreach = True
    return unexplored_address_list


def main_single(file_name, exec_dir, log_dir, idapro_path, verbose):
    global _start_segment_address
    exec_path = os.path.join(exec_dir, file_name)
    angr_path = os.path.join(log_dir, file_name + '.angr')
    log_path = os.path.join(log_dir, file_name + '.log')
    output_path = os.path.join(log_dir, file_name + '.output')
    cmd = 'cp ' + log_path + ' ' + target_dir
    utils.execute_command(cmd)
    new_log_path = os.path.join(target_dir, file_name + '.log')
    binary_info = Binary_Info(exec_path)
    disasm_asm = Disasm_Angr(angr_path)
    _start_segment_address = binary_info.entry_address
    inst_addresses, block_start_addrs = collect_valid_addr_set(idapro_path)
    unexplored_address_list = collect_unreached_addrs(log_path, inst_addresses)
    # print(disasm_asm.address_inst_map)
    # print(block_start_addrs)
    graph = Construct_Graph(log_path, disasm_asm.address_inst_map, inst_addresses, block_start_addrs, unexplored_address_list)
    para_list = neat_main(graph, new_log_path, output_path)
    if verbose:
        print(para_list)
    return para_list


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description='Concolic model checker results checking')
    parser.add_argument('-f', '--file_name', type=str, help='Benchmark file name')
    parser.add_argument('-e', '--elf_dir', default='benchmark/coreutils-build', type=str, help='Benchmark folder name')
    parser.add_argument('-l', '--log_dir', default='benchmark/coreutils-5.3.0-angr', type=str, help='Log folder name')
    parser.add_argument('-i', '--idapro_dir', default='benchmark/coreutils-5.3.0-idapro', type=str, help='IDA Pro disassembled folder name')
    parser.add_argument('-v', '--verbose', default=False, action='store_true', help='Print the starts of unreachable instruction blocks')
    parser.add_argument('-b', '--batch', default=False, action='store_true', help='Run neat_unreach in batch mode')
    args = parser.parse_args()
    utils.make_dir(target_dir)
    elf_dir = os.path.join(utils.PROJECT_DIR, args.elf_dir)
    log_dir = os.path.join(utils.PROJECT_DIR, args.log_dir)
    idapro_path = os.path.join(utils.PROJECT_DIR, os.path.join(args.idapro_dir, args.file_name + '.idapro'))
    # check(log_path, disasm_path + '.idapro', unreach_path)
    main_single(args.file_name, elf_dir, log_dir, idapro_path, args.verbose)
