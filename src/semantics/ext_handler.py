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

from z3 import *
from ..common import lib
from ..common import utils
from ..symbolic import sym_helper
from ..symbolic import sym_engine
from . import smt_helper

def regs_str_to_list(regs):
    regs_split = regs.split(',')
    return [reg.strip() for reg in regs_split]


def set_regs_bottom(store, rip, dests):
    dest_list = regs_str_to_list(dests)
    for dest in dest_list:
        sym_engine.set_sym(store, rip, dest, sym_helper.bottom())


def set_regs_sym(store, rip, dests):
    for dest in dests:
        sym_engine.set_sym(store, rip, dest, sym_helper.gen_sym())
        
def set_segment_regs_sym(store, rip):
    dest_list = lib.SEG_REGS
    for dest in dest_list:
        if dest == 'ds':
            sym_engine.set_sym(store, rip, dest, sym_helper.bit_vec_val_sym(utils.SEGMENT_REG_INIT_VAL))
        else:
            sym_engine.set_sym(store, rip, dest, sym_helper.gen_seg_reg_sym(dest))

def set_reg_val(store, rip, dest, val=0):
    sym_engine.set_sym(store, rip, dest, sym_helper.bit_vec_val_sym(val))


def clear_flags(store):
    for flag in lib.RFlags:
        store[lib.FLAGS][flag] = None
    
def ext_time(store, rip):
    set_regs_sym(store, rip, 'rax')

def ext_srand(store, rip):
    dests = 'rcx, rdx, r9, r10, rsi, rdi'
    set_reg_val(store, rip, 'rax')
    set_regs_sym(store, rip, dests)
    set_reg_val(store, rip, 'r11', 0x1f)
    sym_engine.set_sym(store, rip, 'r8', sym_engine.get_sym(store, rip, 'rdx'))
    clear_flags(store)

def ext_rand(store, rip):
    dests = 'rax, rcx, rdx, r8, rsi, rdi'
    set_regs_sym(store, rip, dests)

def ext_free(store, rip):
    dests = 'rax, rcx, rdx, rsi, rdi'
    set_regs_sym(store, rip, dests)
    clear_flags(store)

def ext_puts(store, rip):
    dests = 'rax, rdi'
    set_regs_sym(store, rip, dests)
    clear_flags(store)

def ext_printf(store, rip):
    dests = 'rax, rcx, rdx, r8, r9, r10, r11, rsi, rdi'
    set_regs_sym(store, rip, dests)

def ext_malloc(store, rip):
    dests = 'rax, rcx, rdx, r8, r9, r10, r11, rsi, rdi'
    set_regs_sym(store, rip, dests)
    
FUNCTION_DICT = {
    'time@GLIBC': ext_time,
    'srand@GLIBC': ext_srand,
    'rand@GLIBC': ext_rand,
    'free@GLIBC': ext_free,
    'puts@GLIBC': ext_puts,
    'printf@GLIBC': ext_printf,
    'malloc@GLIBC': ext_malloc
}


def ext__libc_start_main(store, rip, main_address):
    dests = regs_str_to_list('rcx, rdx, rsi, rdi, r8, r9, r10, r11')
    set_reg_val(store, rip, 'rax', main_address)
    set_regs_sym(store, rip, dests)
    sym_engine.set_sym(store, rip, 'rbp', sym_engine.get_sym(store, main_address, 'rcx'))
    clear_flags(store)
    sym_x = sym_helper.gen_sym_x()
    smt_helper.push_val(store, rip, sym_x)
    

def ext_alloc_mem_call(store, rip, heap_addr, ext_func_name):
    mem_size = sym_engine.get_sym(store, rip, 'rdi')
    mem_addr = sym_helper.bit_vec_val_sym(heap_addr)
    sym_engine.set_sym(store, rip, 'rax', mem_addr)
    if sym_helper.sym_is_int_or_bitvecnum(mem_size):
        mem_size = mem_size.as_long()
    else:
        mem_size = utils.MAX_MALLOC_SIZE
    mem_val = sym_helper.bottom(mem_size) if ext_func_name is not 'calloc' else sym_helper.bit_vec_val_sym(0, mem_size)
    sym_engine.set_mem_sym(store, mem_addr, mem_val, mem_size)
    heap_addr += mem_size
    utils.MAX_HEAP_ADDR = max(utils.MAX_HEAP_ADDR, heap_addr)
    dests = regs_str_to_list('rcx, rdx, rsi, rdi, r8, r9, r10, r11')
    set_regs_sym(store, rip, dests)
    clear_flags(store)
    return heap_addr


def ext_free_mem_call(store, rip):
    mem_addr = sym_engine.get_sym(store, rip, 'rdi')
    if mem_addr in store[lib.MEM]:
        sym_helper.remove_memory_content(store, mem_addr)
    else:
        return 0
    return 1


def ext_rand_call(store, rip):
    ext_func_call(store, rip, 'rand')
    rax_val = sym_engine.get_sym(store, rip, 'rax')
    new_pred = simplify(rax_val >= 0)
    return new_pred


def ext_func_call(store, rip, ext_func_name):
    sym_engine.pollute_all_mem_content(store)
    dests = regs_str_to_list('rax, rcx, rdx, rsi, rdi, r8, r9, r10, r11')
    set_regs_sym(store, rip, dests)
    clear_flags(store)
    
    