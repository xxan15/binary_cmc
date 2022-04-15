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
# python -m src.main -e benchmark/coreutils-5.3.0-bin/bin -l benchmark/coreutils-5.3.0-angr -s 32 -f basename.exe
# python -m src.main -l benchmark/pe_benchmark -e benchmark/pe_benchmark -f ARP.EXE

import os
import time
import argparse
import logging
from .common import utils
from .common import global_var
from .disassembler import helper
from .disassembler.disasm_factory import Disasm_Factory
from .symbolic import sym_helper
from .cfg.cfg import CFG


CHECK_RESULTS = ['', '$\\times$']

def construct_cfg(disasm_asm):
    main_address = global_var.binary_info.main_address
    sym_table = global_var.binary_info.sym_table
    address_sym_table = global_var.binary_info.address_sym_table
    # sym_mem_info_table = global_var.binary_info.sym_mem_info_table
    address_label_map = disasm_asm.address_label_map
    for address in address_label_map:
        address_sym_table[address] = address_label_map[address]
    # function_addr_table = global_var.binary_info.function_addr_table
    # print(address_sym_table)
    # for address in address_sym_table:
    #     print(type(address))
    # print(sym_table)
    # print(disasm_asm.address_ext_func_map)
    # print(global_var.binary_info.sym_mem_info_table)
    # for func_name in function_addr_table:
    #     if func_name != 'main':
    func_name = '_start'
    start_address = global_var.binary_info.entry_address
    main_address = global_var.binary_info.main_address
    constraint_config_file = os.path.join(utils.PROJECT_DIR, utils.PREDEFINED_CONSTRAINT_FILE)
    pre_constraint = sym_helper.parse_predefined_constraint(constraint_config_file)
    # print(global_var.binary_info.dll_func_info)
    # print(disasm_asm.valid_address_no)
    cfg = CFG(sym_table, address_sym_table, disasm_asm.address_inst_map, disasm_asm.address_next_map, start_address, main_address, func_name, disasm_asm.address_ext_func_map, pre_constraint, global_var.binary_info.dll_func_info)
    return cfg


def set_logger(disasm_path, disasm_type, verbose=False):
    for log_name in utils.LOG_NAMES:
        logger_path = disasm_path.replace('.' + disasm_type, '.' + log_name)
        utils.setup_logger(log_name, logger_path, verbose, logging.DEBUG)


def close_logger():
    for log_name in utils.LOG_NAMES:
        utils.close_logger(log_name)


def write_results(cfg):
    num_of_paths, num_of_negatives, num_of_unresolved_indirects, num_of_uninitialized = cfg.cmc_exec_info[0:4]
    reachable_address_num = cfg.reachable_addresses_num()
    utils.output_logger.info('# of reached instructions: ' + str(reachable_address_num))
    utils.output_logger.info('# of paths: ' + str(num_of_paths))
    utils.output_logger.info('# of (possibly) negative paths: ' + str(num_of_negatives))
    utils.output_logger.info('# of uninitialized content: ' + str(num_of_uninitialized))
    utils.output_logger.info('# of unresolved indirects: ' + str(num_of_unresolved_indirects))
    

def cmc_main(exec_path, disasm_path, disasm_type, verbose=False):
    set_logger(disasm_path, disasm_type, verbose)
    global_var.get_binary_info(exec_path)
    helper.disassemble_to_asm(disasm_path)
    disasm_factory = Disasm_Factory(disasm_path, exec_path)
    disasm_asm = disasm_factory.get_disasm()
    # if disasm_asm.valid_address_no >= 10000:
        # print(exec_path)
    start_time = time.time()
    cfg = construct_cfg(disasm_asm)
    exec_time = time.time() - start_time
    write_results(cfg)
    utils.output_logger.info('Execution time (s): ' + str(exec_time))
    close_logger()


def cmc_batch(exec_dir, disasm_dir, disasm_type, verbose=False):
    exec_files = utils.get_executable_files(exec_dir)
    exec_files.sort()
    for exec_path in exec_files:
        file_name = utils.get_file_name(exec_path)
        print(file_name)
        disasm_path = os.path.join(disasm_dir, file_name + '.' + disasm_type)
        try:
            cmc_main(exec_path, disasm_path, disasm_type, verbose)
            time.sleep(15)
        except:
            close_logger()
            time.sleep(15)
            continue


def cmc_specified(file_names, exec_dir, disasm_dir, disasm_type, verbose=False):
    for file_name in file_names:
        exec_path = os.path.join(exec_dir, file_name)
        disasm_path = os.path.join(disasm_dir, file_name + '.' + disasm_type)
        try:
            cmc_main(exec_path, disasm_path, disasm_type, verbose)
            time.sleep(15)
        except:
            close_logger()
            time.sleep(15)
            continue


if __name__=='__main__':
    parser = argparse.ArgumentParser(description='Concolic Model Checker')
    parser.add_argument('-t', '--disasm_type', default='idapro', type=str, help='Disassembler')
    parser.add_argument('-b', '--batch', default=False, action='store_true', help='Run cmc_main in batch mode') 
    parser.add_argument('-l', '--log_dir', default='benchmark/coreutils-idapro', type=str, help='Benchmark library') 
    parser.add_argument('-e', '--exec_dir', default='benchmark/coreutils-build/src', type=str, help='Elf shared object library') 
    parser.add_argument('-f', '--file_name', type=str, help='Benchmark file name')
    parser.add_argument('-v', '--verbose', default=False, action='store_true', help='Whether to print log information on the screen')
    parser.add_argument('-c', '--bmc_bound', default=25, type=int, help='The default value of the BMC bound')
    parser.add_argument('-s', '--mem_addr_size', default=32, type=int, help='The default value of the memory address size')
    args = parser.parse_args()
    utils.MAX_VISIT_COUNT = args.bmc_bound
    utils.MEM_ADDR_SIZE = args.mem_addr_size
    disasm_type = args.disasm_type
    file_name = args.file_name
    log_dir = os.path.join(utils.PROJECT_DIR, args.log_dir)
    exec_dir = os.path.join(utils.PROJECT_DIR, args.exec_dir)
    if args.batch:
        cmc_batch(exec_dir, log_dir, disasm_type, args.verbose)
    else:
        disasm_path = os.path.join(log_dir, file_name + '.' + disasm_type)
        exec_path = os.path.join(exec_dir, file_name)
        cmc_main(exec_path, disasm_path, disasm_type, args.verbose)
    
    # file_names = ['basename.exe', 'expand.exe', 'link.exe', 'mknod.exe', 'uname.exe', 'realpath.exe', 'comm.exe', 'echo.exe', 'dir.exe']
    # cmc_specified(file_names, exec_dir, disasm_lib_dir, disasm_type, args.verbose)
    
    
        