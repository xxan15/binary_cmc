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

import sys
from z3 import *
from ..common import lib
from ..common import utils
from ..symbolic import sym_helper
from ..symbolic import sym_engine
from . import smt_helper

def regs_str_to_list(regs):
    regs_split = regs.split(',')
    return [reg.strip() for reg in regs_split]


def set_regs_bottom(store, rip, dests, block_id):
    dest_list = regs_str_to_list(dests)
    for dest in dest_list:
        sym_engine.set_sym(store, rip, dest, sym_helper.bottom(), block_id)


def set_regs_sym(store, rip, dests, block_id):
    for dest in dests:
        sym_engine.set_sym(store, rip, dest, sym_helper.gen_sym(), block_id)
        
def set_segment_regs_sym(store, rip):
    dest_list = lib.SEG_REGS
    for dest in dest_list:
        if dest == 'ds':
            sym_engine.set_sym(store, rip, dest, sym_helper.bit_vec_val_sym(utils.SEGMENT_REG_INIT_VAL), 0)
        else:
            sym_engine.set_sym(store, rip, dest, sym_helper.gen_seg_reg_sym(dest), 0)

def set_reg_val(store, rip, dest, val, block_id):
    sym_engine.set_sym(store, rip, dest, sym_helper.bit_vec_val_sym(val), block_id)


def clear_flags(store):
    for flag in lib.RFlags:
        store[lib.FLAGS][flag] = None
    

def insert_termination_symbol(store, rip, block_id):
    sym_x = sym_helper.gen_sym_x()
    smt_helper.push_val(store, rip, sym_x, block_id)


def ext__libc_start_main(store, rip, main_address, block_id, inv_names):
    dests = regs_str_to_list('rcx, rdx, rsi, rdi, r8, r9, r10, r11')
    # for inv_name in inv_names:
    #     if inv_name in dests:
    #         dests.remove(inv_name)
    set_reg_val(store, rip, 'rax', main_address, block_id)
    set_regs_sym(store, rip, dests, block_id)
    sym_engine.set_sym(store, rip, 'rbp', sym_engine.get_sym(store, main_address, 'rcx', block_id), block_id)
    clear_flags(store)
    insert_termination_symbol(store, rip, block_id)
    

def ext_gen_fresh_heap_pointer(store, rip, ext_func_name, block_id, mem_size):
    heap_addr = store[lib.HEAP_ADDR]
    mem_addr = sym_helper.bit_vec_val_sym(heap_addr)
    sym_engine.set_sym(store, rip, 'rax', mem_addr, block_id)
    if sym_helper.sym_is_int_or_bitvecnum(mem_size):
        mem_size = mem_size.as_long()
    else:
        mem_size = utils.MAX_MALLOC_SIZE
    if mem_size == 0:
        sys.exit('The allocation size for ' + ext_func_name + ' function cannot be zero')
    mem_val = sym_helper.bottom(mem_size) if ext_func_name is not 'calloc' else sym_helper.bit_vec_val_sym(0, mem_size)
    heap_addr += mem_size
    utils.MAX_HEAP_ADDR = max(utils.MAX_HEAP_ADDR, heap_addr)
    sym_engine.set_mem_sym(store, mem_addr, mem_val, mem_size)
    dests = regs_str_to_list('rcx, rdx, rsi, rdi, r8, r9, r10, r11')
    set_regs_sym(store, rip, dests, block_id)
    clear_flags(store)
    store[lib.HEAP_ADDR] = heap_addr
    

def ext_alloc_mem_call(store, rip, ext_func_name, block_id):
    heap_addr = store[lib.HEAP_ADDR]
    utils.logger.info(heap_addr)
    mem_size = sym_engine.get_sym(store, rip, 'rdi', block_id) if ext_func_name in ('malloc', 'calloc') else sym_engine.get_sym(store, rip, 'rsi', block_id)
    mem_addr = sym_helper.bit_vec_val_sym(heap_addr)
    sym_engine.set_sym(store, rip, 'rax', mem_addr, block_id)
    if sym_helper.sym_is_int_or_bitvecnum(mem_size):
        mem_size = mem_size.as_long()
    else:
        mem_size = utils.MAX_MALLOC_SIZE
    if mem_size == 0:
        sys.exit('The allocation size for ' + ext_func_name + ' function cannot be zero')
    mem_val = sym_helper.bottom(mem_size) if ext_func_name is not 'calloc' else sym_helper.bit_vec_val_sym(0, mem_size)
    heap_addr += mem_size
    utils.MAX_HEAP_ADDR = max(utils.MAX_HEAP_ADDR, heap_addr)
    sym_engine.set_mem_sym(store, mem_addr, mem_val, mem_size)
    dests = regs_str_to_list('rcx, rdx, rsi, rdi, r8, r9, r10, r11')
    set_regs_sym(store, rip, dests, block_id)
    clear_flags(store)
    store[lib.HEAP_ADDR] = heap_addr


def ext_free_mem_call(store, rip, block_id):
    succeed = True
    mem_addr = sym_engine.get_sym(store, rip, 'rdi', block_id)
    if mem_addr in store[lib.MEM]:
        sym_helper.remove_memory_content(store, mem_addr)
    elif sym_helper.sym_is_int_or_bitvecnum(mem_addr):
        succeed = False
        utils.logger.error('Error: Use after free at address ' + str(mem_addr) + ' while memory content at address ' + str(mem_addr) + ' is freed while there is no record in the global memory state')
        utils.output_logger.error('Error: Use after free at address ' + str(mem_addr) +' while memory content at address ' + str(mem_addr) + ' is freed while there is no record in the global memory state')
        store[lib.POINTER_RELATED_ERROR] = lib.MEMORY_RELATED_ERROR_TYPE.USE_AFTER_FREE
    return succeed


def ext_func_call(store, rip, block_id, mem_preserve_assumption):
    dests = lib.CALLEE_NOT_SAVED_REGS
    if not mem_preserve_assumption:
        sym_engine.pollute_all_mem_content(store, block_id)
    set_regs_sym(store, rip, dests, block_id)
    clear_flags(store)
    
    