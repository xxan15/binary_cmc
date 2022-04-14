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

# python -m src.check.check_reachability -e benchmark/pe_benchmark -l benchmark/pe_benchmark -f HOSTNAME.EXE -v
# python -m src.check.check_reachability -e benchmark/coreutils-5.3.0-bin/bin -l benchmark/coreutils-5.3.0-idapro -f basename.exe -v

import os
import re
import time
import argparse
from enum import Enum
from urllib.robotparser import RequestRate

from ..common import lib
from ..common import utils
from ..binary.binary_info import Binary_Info
from ..disassembler.disasm_idapro import Disasm_IDAPro
from .construct_graph import Construct_Graph

target_dir = os.path.join(utils.PROJECT_DIR, 'temp')

address_inst_pattern = re.compile('^[.a-zA-Z]+:[0-9a-zA-Z]+[ ]{17}[a-zA-Z]')

imm_pat = re.compile('^0x[0-9a-fA-F]+$|^[0-9]+$|^-[0-9]+$|^-0x[0-9a-fA-F]+$|^[0-9a-fA-F]+$|^-[0-9a-fA-F]+$')

variable_expr_pat = re.compile(r'^[.a-zA-Z_0-9]+:[0-9a-zA-Z]{16} [a-zA-Z0-9_@]+|^[.a-zA-Z_0-9]+:[0-9a-zA-Z]{8} [a-zA-Z0-9_@]+')

non_inst_prefix = ('dd ', 'dw', 'db', 'text ', 'align', 'assume', 'public', 'start', 'type')


class UNREACHED_TYPE(Enum):
    UNREACHED_CONDITIONAL = 0
    UNREACHED_NO_EXPLICIT_ENTRIES = 1
    UNREACHED_ENTRIES_CONDITIONAL = 2
    UNREACHED_ENTRIES_NO_EXPLICIT = 3


def is_located_at_code_segments(line):
    return line.startswith(lib.CODE_SEGMENTS)


def append_all_addresses(start_address, end_address, inst_addresses, address_inst_map, graph):
    res = ''
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
                    res += utils.u_hex(address) + ': ' + inst + '\n'
    res += '\n'
    return res, cnt



def find_start_addr(inst_addresses, address):
    for idx in range(len(inst_addresses) - 1):
        curr_addr = inst_addresses[idx]
        next_addr = inst_addresses[idx + 1]
        if address >= curr_addr and address < next_addr:
            return curr_addr
    return inst_addresses[-1]

    
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


def string_of_unreached_class(unreached_class):
    res = ''
    if unreached_class == UNREACHED_TYPE.UNREACHED_CONDITIONAL:
        res = 'conditional jump (upperbound is hit)'
    elif unreached_class == UNREACHED_TYPE.UNREACHED_ENTRIES_CONDITIONAL:
        res = 'conditional entries not reached (upperbound is hit)'
    elif unreached_class == UNREACHED_TYPE.UNREACHED_NO_EXPLICIT_ENTRIES:
        res = 'implicit called function or unresolved indirect jump'
    else:
        res = 'dynamic entries not reached'
    return res
    
    

def reconstruct_new_content(start_address_list, end_address_list, graph):
    global unreached_class_map
    content = ''
    inst_addresses = graph.inst_addresses
    address_inst_map = graph.address_inst_map
    address_entries_map = graph.address_entries_map
    for start_address, end_address in zip(start_address_list, end_address_list):
        res, _ = append_all_addresses(start_address, end_address, inst_addresses, address_inst_map, graph)
        unreached_class = unreached_class_map[start_address]
        content +='unreached due to ' + string_of_unreached_class(unreached_class) + '\n'
        if start_address in address_entries_map:
            entries = address_entries_map[start_address]
            start_entries = [entry_start_addr_map[i] if i in entry_start_addr_map else i for i in entries]
            content += str([hex(i).split('0x', 1)[1].strip() for i in start_entries]) + '\n'
        content += res + '\n'
    return content


def construct_entry_start_addr_map(address_entries_map, start_address_list, start_address):
    global entry_start_addr_map
    for entry_address in address_entries_map[start_address]:
        if entry_address not in entry_start_addr_map:
            entry_start_addr = find_start_addr(start_address_list, entry_address)
            entry_start_addr_map[entry_address] = entry_start_addr
        else:
            entry_start_addr = entry_start_addr_map[entry_address]


def judge_unreached_block_type(address_entries_map, address_inst_map, graph, inst_addresses, start_address, end_address):
    global cond_jump_unreached_cnt, implicit_called_cnt, unreached_class_map, entry_start_addr_map, max_entries_num
    unreached_entries = True
    for entry_address in address_entries_map[start_address]:
        entry_start_addr = entry_start_addr_map[entry_address]
        base_idx = 0
        tmp_entry_addr = entry_start_addr
        trace = [entry_start_addr]
        while tmp_entry_addr not in unreached_class_map:
            tmp_entry_addrs = address_entries_map[tmp_entry_addr]
            idx = min(base_idx, len(tmp_entry_addrs) - 1)
            tmp_entry_addr = entry_start_addr_map[tmp_entry_addrs[idx]]
            if tmp_entry_addr in trace:
                idx = trace.index(tmp_entry_addr)
                trace = trace[:idx]
                base_idx += 1
            trace.append(tmp_entry_addr)
            if base_idx == max_entries_num:
                break
        if tmp_entry_addr in unreached_class_map:
            if unreached_class_map[tmp_entry_addr] == UNREACHED_TYPE.UNREACHED_CONDITIONAL:
                _, cnt = append_all_addresses(start_address, end_address, inst_addresses, address_inst_map, graph)
                unreached_class_map[start_address] = UNREACHED_TYPE.UNREACHED_ENTRIES_CONDITIONAL
                cond_jump_unreached_cnt += cnt
                unreached_entries = False
                break
    if unreached_entries:
        _, cnt = append_all_addresses(start_address, end_address, inst_addresses, address_inst_map, graph)
        unreached_class_map[start_address] = UNREACHED_TYPE.UNREACHED_ENTRIES_NO_EXPLICIT
        implicit_called_cnt += cnt


def count_refined_implicit_called_functions(start_address_list, graph):
    global cond_jump_unreached_cnt, implicit_called_cnt, unreached_class_map, undecided_addr_info, entry_start_addr_map, max_entries_num
    entry_start_addr_map = {}
    inst_addresses = graph.inst_addresses
    address_inst_map = graph.address_inst_map
    address_entries_map = graph.address_entries_map
    for start_address in undecided_addr_info:
        construct_entry_start_addr_map(address_entries_map, start_address_list, start_address)
    max_entries_num = -1
    for addr in address_entries_map:
        addr_entries = address_entries_map[addr]
        max_entries_num = max(max_entries_num, len(addr_entries))
    for start_address in undecided_addr_info:
        end_address = undecided_addr_info[start_address]
        judge_unreached_block_type(address_entries_map, address_inst_map, graph, inst_addresses, start_address, end_address)


def count_implicit_called_functions(start_address_list, end_address_list, unreach_addresses, graph):
    global cond_jump_unreached_cnt, implicit_called_cnt, unreached_class_map, undecided_addr_info
    unreached_class_map = {}
    undecided_addr_info = {}
    inst_addresses = graph.inst_addresses
    address_inst_map = graph.address_inst_map
    address_entries_map = graph.address_entries_map
    # print(str([hex(i) + ':' + str(address_entries_map[i]) for i in address_entries_map]))
    for start_address, end_address in zip(start_address_list, end_address_list):
        if start_address in graph.block_start_addrs:
            if start_address in address_entries_map:
                undecided_entry = True
                for entry_address in address_entries_map[start_address]:
                    # If the entry point to the address is reachable
                    if entry_address not in unreach_addresses:
                        unreached_class_map[start_address] = UNREACHED_TYPE.UNREACHED_CONDITIONAL
                        _, cnt = append_all_addresses(start_address, end_address, inst_addresses, address_inst_map, graph)
                        cond_jump_unreached_cnt += cnt
                        undecided_entry = False
                        # c_blk_cnt += 1
                        break
                if undecided_entry:
                    undecided_addr_info[start_address] = end_address
            else:
                # No explicit entries for these unreached blocks
                _, cnt = append_all_addresses(start_address, end_address, inst_addresses, address_inst_map, graph)
                unreached_class_map[start_address] = UNREACHED_TYPE.UNREACHED_NO_EXPLICIT_ENTRIES
                implicit_called_cnt += cnt
                # i_blk_cnt += 1
        else:
            # The starting address of the unreached block is not the starting address of any block divided by IDA Pro
            # Before the starting address, there should be some conditional jump instruction
            tmp_start_addr = find_start_addr(start_address_list, start_address)
            _, cnt = append_all_addresses(start_address, end_address, inst_addresses, address_inst_map, graph)
            unreached_class_map[start_address] = UNREACHED_TYPE.UNREACHED_CONDITIONAL            
            cond_jump_unreached_cnt += cnt
    # print(str([hex(i) + ':' + str(unreached_class_map[i]) for i in unreached_class_map]))
    count_refined_implicit_called_functions(start_address_list, graph)


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
    start_address_list, end_address_list = divide_to_block(new_content)
    count_implicit_called_functions(start_address_list, end_address_list, unreach_addresses, graph)
    new_content = reconstruct_new_content(start_address_list, end_address_list, graph)
    # print(new_content)
    with open(new_log_path, 'w+') as f:
        f.write(new_content)
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
                elif '# of (possibly) negative paths' in line:
                    neg_path_cnt = int(line.rsplit(' ', 1)[1])
                elif '# of unresolved indirects' in line:
                    indirects_cnt = int(line.rsplit(' ', 1)[1])
                elif 'Execution time ' in line:
                    exec_time = float(line.rsplit(' ', 1)[1])
    res_list.append(reached_cnt)
    res_list.append(path_cnt)
    res_list.append(neg_path_cnt)
    res_list.append(indirects_cnt)
    return res_list, exec_time


def neat_main(graph, new_log_path, output_path):
    global cond_jump_unreached_cnt, implicit_called_cnt
    cond_jump_unreached_cnt, implicit_called_cnt = 0, 0
    normalize_unreachable(new_log_path, graph)
    para_list, exec_time = read_parameters(output_path)
    # para_list.append(unreached_count)
    # para_list.append(blk_count)
    para_list.append(cond_jump_unreached_cnt)
    # para_list.append(c_blk_cnt)
    para_list.append(implicit_called_cnt)
    # para_list.append(i_blk_cnt)
    # para_list.append(unreached_entries_cnt)
    # para_list.append(u_blk_cnt)
    para_list.append(exec_time)
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
                        #     else:
                        #         in_block = False
                        #         # invalid_address_set.add(address)
                        # else:
                        #     in_block = False
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
    # inst_addresses = []
    # for address in address_set:
    #     inst_addresses.append(address)
    # inst_addresses.sort()
    return block_start_addrs


def pp_para_list(file_name, para_list, print_type, combine):
    sep = '\t' if print_type == 0 else ' & '
    res = file_name + sep
    unreached = 0
    for i in range(len(para_list)):
        val = para_list[i]
        if i < 4:
            res += str(val) + sep
        elif i == 4: 
            if combine:
                unreached += val
            else:
                res += str(val) + sep
        elif i == 5:
            if print_type != 0:
                if combine:
                    unreached += val
                    res += str(unreached)
                else:
                    res += str(val)
            else:
                if combine:
                    unreached += val
                    res += str(unreached) + sep
                else:
                    res += str(val) + sep
        elif i == 6:
            if print_type != 0:
                pass
            else:
                res += str(val)
    if print_type != 0:
        res += ' \\\\'
        # res += '\n\\midrule'
    print(res)

def main_single(file_name, exec_dir, log_dir, idapro_path, verbose, print_type, combine):
    global _start_segment_address
    exec_path = os.path.join(exec_dir, file_name)
    log_path = os.path.join(log_dir, file_name + '.log')
    output_path = os.path.join(log_dir, file_name + '.output')
    cmd = 'cp ' + log_path + ' ' + target_dir
    utils.execute_command(cmd)
    new_log_path = os.path.join(target_dir, file_name + '.log')
    binary_info = Binary_Info(exec_path)
    disasm_asm = Disasm_IDAPro(idapro_path)
    _start_segment_address = binary_info.entry_address
    inst_addresses = list(disasm_asm.address_inst_map.keys())
    inst_addresses.sort()
    block_start_addrs = collect_valid_addr_set(idapro_path)
    # print(disasm_asm.address_inst_map)
    # print(block_start_addrs)
    graph = Construct_Graph(log_path, disasm_asm.address_inst_map, inst_addresses, block_start_addrs)
    para_list = neat_main(graph, new_log_path, output_path)
    if verbose:
        pp_para_list(file_name, para_list, print_type, combine)
    return para_list


def main_batch(exec_dir, log_dir, verbose, print_type, combine):
    exec_files = utils.get_executable_files(exec_dir)
    exec_files.sort()
    for exec_path in exec_files:
        file_name = utils.get_file_name(exec_path)
        # print(file_name)
        idapro_path = os.path.join(utils.PROJECT_DIR, os.path.join(log_dir, file_name + '.idapro'))
        main_single(file_name, exec_dir, log_dir, idapro_path, verbose, print_type, combine)
        time.sleep(5)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description='Concolic model checker results checking')
    parser.add_argument('-f', '--file_name', type=str, help='Benchmark file name')
    parser.add_argument('-e', '--exec_dir', default='benchmark/coreutils-build', type=str, help='Benchmark folder name')
    parser.add_argument('-l', '--log_dir', default='benchmark/coreutils-5.3.0-idapro', type=str, help='Log folder name')
    parser.add_argument('-v', '--verbose', default=False, action='store_true', help='Print the starts of unreachable instruction blocks')
    parser.add_argument('-t', '--print_type', default=0, help='Print the output in specific format')
    parser.add_argument('-c', '--combine', default=False, action='store_true', help='Whether the add the unreached instrs together')
    parser.add_argument('-b', '--batch', default=False, action='store_true', help='Run neat_unreach in batch mode')
    args = parser.parse_args()
    utils.make_dir(target_dir)
    exec_dir = os.path.join(utils.PROJECT_DIR, args.exec_dir)
    log_dir = os.path.join(utils.PROJECT_DIR, args.log_dir)
    if args.batch:
        # for file_name in ['seq.exe', 'setuidgid.exe', 'sha1sum.exe', 'sleep.exe', 'stty.exe', 'sum.exe', 'sync.exe', 'tee.exe', 'tr.exe', 'true.exe', 'tsort.exe', 'tty.exe', 'uname.exe', 'unexpand.exe', 'uniq.exe', 'unlink.exe', 'uptime.exe', 'users.exe', 'whoami.exe', 'yes.exe']:
        main_batch(exec_dir, log_dir, args.verbose, args.print_type, args.combine)
        time.sleep(5)
    else:
        idapro_path = os.path.join(utils.PROJECT_DIR, os.path.join(args.log_dir, args.file_name + '.idapro'))
        file_name = args.file_name
        main_single(file_name, exec_dir, log_dir, idapro_path, args.verbose, args.print_type, args.combine)
    
