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

# python -m src.main -l micro-benchmark -e micro-benchmark -f filename

import os
import time
import argparse
import logging
from .common import utils
from .common import global_var
from .disassembler import helper
from .disassembler.disasm_factory import Disasm_Factory
from .cfg.cfg import CFG
from .cfg.cfg_context_free import CFG_Context_Free


CHECK_RESULTS = ['', '$\\times$']

def construct_cfg(disasm_path, disasm_asm):
    main_address = global_var.elf_info.main_address
    sym_table = global_var.elf_info.sym_table
    address_sym_table = global_var.elf_info.address_sym_table
    # sym_mem_info_table = global_var.elf_info.sym_mem_info_table
    address_label_map = disasm_asm.address_label_map
    for address in address_label_map:
        if address not in address_sym_table:
            address_sym_table[address] = address_label_map[address]
    function_addr_table = global_var.elf_info.function_addr_table
    # print(address_sym_table)
    # print(sym_table)
    # print(global_var.elf_info.sym_mem_info_table)
    # for func_name in function_addr_table:
    #     if func_name != 'main':
    func_name = '_start'
    start_address = function_addr_table[func_name]
    cfg = CFG_Context_Free(sym_table, address_sym_table, disasm_asm.address_inst_map, disasm_asm.address_next_map, start_address, main_address, func_name, disasm_asm.func_call_order)
    callgraph_path = disasm_path.rsplit('.', 1)[0].strip()
    cfg.draw_callgraph(callgraph_path)
    write_results(disasm_asm, cfg)


def set_logger(disasm_path, disasm_type, verbose=False):
    for log_name in utils.LOG_NAMES:
        logger_path = disasm_path.replace('.' + disasm_type, '.' + log_name)
        utils.setup_logger(log_name, logger_path, verbose, logging.DEBUG)


def close_logger():
    for log_name in utils.LOG_NAMES:
        utils.close_logger(log_name)


def write_results(disasm_asm, cfg):
    num_of_verified_functions = len(cfg.func_call_order)
    num_of_paths, num_of_positives, num_of_negatives = cfg.cmc_exec_info[0:3]
    reachable_address_num = cfg.reachable_addresses_num()
    utils.output_logger.info('# of reachable instructions: ' + str(reachable_address_num))
    utils.output_logger.info('# of verified functions: ' + str(num_of_verified_functions))
    utils.output_logger.info('# of paths: ' + str(num_of_paths))
    utils.output_logger.info('# of sound paths: ' + str(num_of_positives))
    utils.output_logger.info('# of unsound paths: ' + str(num_of_negatives))
    

def cmc_main(exec_path, disasm_path, disasm_type, verbose=False):
    set_logger(disasm_path, disasm_type, verbose)
    global_var.get_elf_info(exec_path)
    helper.disassemble_to_asm(exec_path, disasm_path, disasm_type)
    disasm_factory = Disasm_Factory(disasm_path, disasm_type)
    disasm_asm = disasm_factory.get_disasm()
    # start_time = time.time()
    construct_cfg(disasm_path, disasm_asm)
    # exec_time = time.time() - start_time
    # utils.logger.info(exec_time)
    close_logger()


def cmc_batch(elf_lib_dir, disasm_lib_dir, disasm_type, verbose=False):
    disasm_files = [os.path.join(dp, f) for dp, dn, filenames in os.walk(disasm_lib_dir) for f in filenames if f.endswith(disasm_type)]
    disasm_files.sort()
    for disasm_path in disasm_files:
        file_name = utils.get_file_name(disasm_path)
        print(file_name)
        exec_path = os.path.join(elf_lib_dir, file_name)
        if os.path.exists(exec_path):
            try:
                cmc_main(exec_path, disasm_path, disasm_type, verbose)
                time.sleep(15)
            except:
                close_logger()
                time.sleep(15)
                continue


def cmc_specified(file_names, elf_lib_dir, disasm_lib_dir, disasm_type, verbose=False):
    for file_name in file_names:
        exec_path = os.path.join(elf_lib_dir, file_name)
        disasm_path = os.path.join(disasm_lib_dir, file_name + '.' + disasm_type)
        try:
            cmc_main(exec_path, disasm_path, disasm_type, verbose)
            time.sleep(15)
        except:
            close_logger()
            time.sleep(15)
            continue


if __name__=='__main__':
    parser = argparse.ArgumentParser(description='Concolic Model Checker')
    parser.add_argument('-t', '--disasm_type', default='objdump', type=str, help='Disassembler')
    parser.add_argument('-b', '--batch', default=False, action='store_true', help='Run cmc_main in batch mode') 
    parser.add_argument('-l', '--log_dir', default='benchmark/coreutils-objdump', type=str, help='Benchmark library') 
    parser.add_argument('-e', '--elf_dir', default='benchmark/coreutils-build', type=str, help='Elf shared object library') 
    parser.add_argument('-f', '--file_name', type=str, help='Benchmark file name')
    parser.add_argument('-v', '--verbose', default=False, action='store_true', help='Whether to print log information on the screen')
    parser.add_argument('-c', '--bmc_bound', default=25, type=int, help='The default value of the BMC bound')
    args = parser.parse_args()
    utils.MAX_VISIT_COUNT = args.bmc_bound
    disasm_type = args.disasm_type
    log_dir = args.log_dir
    if disasm_type != 'objdump' and 'objdump' in args.log_dir:
        log_dir = log_dir.replace('objdump', disasm_type)
    disasm_lib_dir = os.path.join(utils.PROJECT_DIR, log_dir)
    elf_lib_dir = os.path.join(utils.PROJECT_DIR, args.elf_dir)
    if args.batch:
        cmc_batch(elf_lib_dir, disasm_lib_dir, disasm_type, args.verbose)
    else:
        disasm_path = os.path.join(disasm_lib_dir, args.file_name + '.' + disasm_type)
        exec_path = os.path.join(elf_lib_dir, args.file_name)
        cmc_main(exec_path, disasm_path, disasm_type, args.verbose)
    # 
    # file_names = ['basename', 'expand', 'link', 'mknod', 'uname', 'realpath', 'comm', 'echo', 'dir']
    # cmc_specified(file_names, elf_lib_dir, disasm_lib_dir, disasm_type, args.verbose)
    # 
    
        