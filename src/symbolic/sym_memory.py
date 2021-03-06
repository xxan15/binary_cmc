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
import sys
from z3 import *
from ..common import lib
from ..common import utils
from . import sym_helper
from . import sym_register
from ..common import global_var
from ..common.lib import MEMORY_RELATED_ERROR_TYPE

letter_num_neg_pat = re.compile(r'\w+')
sym_pat = re.compile(r'\W+')


def get_sym_val(str_val, store, length):
    res = None
    if str_val in lib.REG_NAMES:
        res = sym_register.get_register_sym(store, str_val)
    elif utils.imm_pat.match(str_val):
        res = BitVecVal(utils.imm_str_to_int(str_val), length)
    elif str_val in lib.SEG_REGS:
        res = store[lib.SEG][str_val]
    else:
        res = BitVec(str_val, length)
    return res


def get_idx_sym_val(store, arg, src_sym, src_val, length):
    res = None
    if arg in lib.REG_NAMES:
        res = sym_register.get_register_sym(store, arg)
        if not sym_helper.is_bit_vec_num(res):
            m = sym_helper.check_pred_satisfiable([src_sym == src_val])
            if m is not False:
                for d in m.decls():
                    s_val = m[d]
                    s_len = s_val.size()
                    res = substitute(res, (BitVec(d.name(), s_len), s_val))
                res = simplify(res)
    elif utils.imm_pat.match(arg):
        res = BitVecVal(utils.imm_str_to_int(arg), length)
    return res

def calc_mult(stack, op_stack):
    res = stack[0]
    for idx, op in enumerate(op_stack):
        if op == '*':
            res = stack[idx] * stack[idx + 1]
            stack[idx] = simplify(res)
            del stack[idx + 1]
            del op_stack[idx]


def eval_simple_formula(stack, op_stack):
    calc_mult(stack, op_stack)
    res = stack[0]
    for idx, op in enumerate(op_stack):
        if op == '+':
            res = res + stack[idx + 1]
        elif op == '-':
            res = res - stack[idx + 1]
        else:
            utils.logger.debug('There are unrecognized operator ' + op)
    return simplify(res)


# line: 'rax + rbx * 1 + 0'
# line: 'rbp - 0x14'
# line: 'rax'
def calc_effective_address(line, store, length):
    stack = []
    op_stack = []
    line = line.strip()
    while line:
        lsi = letter_num_neg_pat.match(line)
        if lsi:
            lsi = lsi.group(0)
            val = get_sym_val(lsi, store, length)
            stack.append(val)
        else:
            lsi = sym_pat.match(line)
            lsi = lsi.group(0).strip()
            op_stack.append(lsi)
        line = line.split(lsi, 1)[1].strip()
    res = eval_simple_formula(stack, op_stack)
    return res


# arg: DWORD PTR [rcx+rdx*4]
def get_jump_table_address(store, arg, src_sym, src_val, length=utils.MEM_ADDR_SIZE):
    arg = utils.extract_content(arg, '[')
    stack = []
    op_stack = []
    arg = arg.strip()
    while arg:
        ai = letter_num_neg_pat.match(arg)
        if ai:
            ai = ai.group(0)
            val = get_idx_sym_val(store, ai, src_sym, src_val, length)
            stack.append(val)
        else:
            ai = sym_pat.match(arg)
            ai = ai.group(0).strip()
            op_stack.append(ai)
        arg = arg.split(ai, 1)[1].strip()
    res = eval_simple_formula(stack, op_stack)
    return res


def get_effective_address(store, rip, src, length=utils.MEM_ADDR_SIZE):
    res = None
    if src.endswith(']'):
        res = utils.extract_content(src, '[')
        if utils.imm_pat.match(res):
            res = BitVecVal(utils.imm_str_to_int(res), length)
        elif 'rip' in res:  # 'rip+0x2009a6'
            res = res.replace('rip', hex(rip))
            res = eval(res)
            res = BitVecVal(res & 0xffffffffffffffff, length)
        else:  # 'rax + rbx * 1'
            lsi_group = letter_num_neg_pat.match(res)
            if lsi_group:
                lsi = lsi_group.group(0)
                if lsi in lib.REG_INFO_DICT:
                    _, _, length = lib.REG_INFO_DICT[lsi]
                elif lsi in lib.REG64_NAMES:
                    length = 64
            res = calc_effective_address(res, store, length)
    elif 's:' in src:
        seg_name, new_src = src.split(':', 1)
        seg_addr = get_sym_val(seg_name.strip(), store, length)
        new_addr = get_effective_address(store, rip, new_src.strip(), length)
        res = simplify(seg_addr + new_addr)
    elif utils.imm_pat.match(src):
        res = BitVecVal(utils.imm_str_to_int(src), length)
    else:
        utils.logger.debug('Cannot recognize the effective address of ' + src)
    return res


def reset_mem_content_pollute(store, block_id):
    store[lib.MEM_CONTENT_POLLUTED] = block_id


def pollute_all_mem_content(store, block_id):
    store[lib.MEM_CONTENT_POLLUTED] = block_id
    addr_list = list(store[lib.MEM].keys())
    for addr in addr_list:
        if not sym_helper.sym_is_int_or_bitvecnum(addr):
            if sym_helper.sym_is_int_or_bitvecnum(store[lib.MEM][addr][0]):
                store[lib.MEM][addr] = [sym_helper.gen_sym(store[lib.MEM][addr][0].size()), block_id]
        else:
            int_addr = sym_helper.int_from_sym(addr)
            if int_addr >= utils.MIN_HEAP_ADDR and int_addr < utils.MAX_HEAP_ADDR:
                if sym_helper.sym_is_int_or_bitvecnum(store[lib.MEM][addr][0]):
                    store[lib.MEM][addr] = [sym_helper.gen_sym(store[lib.MEM][addr][0].size()), block_id]


def pollute_mem_w_sym_address(store, block_id):
    for addr in store[lib.MEM]:
        if not sym_helper.sym_is_int_or_bitvecnum(addr):
            if sym_helper.sym_is_int_or_bitvecnum(store[lib.MEM][addr][0]):
                store[lib.MEM][addr] = [sym_helper.gen_sym(store[lib.MEM][addr][0].size()), block_id]


def check_mem_addr_overlapping(store, address, byte_sz, store_key=lib.MEM):
    overlapping = False
    if sym_helper.is_bit_vec_num(address):
        int_address = address.as_long()
        if not sym_helper.addr_in_stack_section(int_address):
            for offset in range(-3, byte_sz):
                if offset != 0:
                    curr_address = simplify(address + offset)
                    if curr_address in store[store_key]:
                        prev_sym = store[store_key][curr_address][0]
                        prev_sz = prev_sym.size() // 8
                        if (offset < 0 and prev_sz > -offset) or offset > 0:
                            overlapping = True
                            store[lib.POINTER_RELATED_ERROR] = (MEMORY_RELATED_ERROR_TYPE.BUFFER_OVERFLOW, int_address)
                            break
    return overlapping



def set_mem_sym_val(store, address, sym, block_id, length=utils.MEM_ADDR_SIZE, store_key=lib.MEM): 
    byte_sz = length // 8
    if check_mem_addr_overlapping(store, address, byte_sz, store_key): return
    if address in store[store_key]:
        prev_sym = store[store_key][address][0]
        prev_sz = prev_sym.size() // 8
        if byte_sz < prev_sz:
            rest_sym = sym_helper.extract_bytes(prev_sz, byte_sz, prev_sym)
            curr_sym = simplify(Concat(rest_sym, sym))
            store[store_key][address] = [curr_sym, block_id]
        else:
            store[store_key][address] = [sym, block_id]
    else:
        store[store_key][address] = [sym, block_id]


def is_mem_addr_in_stdout(store, address):
    res = None
    if lib.STDOUT_HANDLER in store:
        stdout_handler = store[lib.STDOUT_HANDLER]
        tmp = simplify(address - stdout_handler)
        if sym_helper.is_bit_vec_num(tmp):
            res = tmp
        else:
            tmp = simplify(address - sym_helper.STDOUT_ADDR)
            if sym_helper.is_bit_vec_num(tmp):
                res = address
    return res


def set_mem_sym(store, address, sym, block_id, length=utils.MEM_ADDR_SIZE):
    # If the memory address is not concrete
    if not sym_helper.sym_is_int_or_bitvecnum(address):
        tmp = is_mem_addr_in_stdout(store, address)
        if tmp is not None:
            set_mem_sym_val(store, tmp, sym, block_id, length, lib.STDOUT)
        else:
            store[lib.MEM][address] =[sym, block_id]
    else:
        set_mem_sym_val(store, address, sym, block_id, length)


def get_mem_sym(store, address, length=utils.MEM_ADDR_SIZE, store_key=lib.MEM):
    res = None
    if address in store[store_key]:
        sym = store[store_key][address][0]
        sym_len = sym.size()
        if sym_len > length:
            res = simplify(Extract(length - 1, 0, sym))
        elif sym_len == length:
            res = sym
    return res


def read_mem_error_report(store, int_address):
    if sym_helper.addr_in_heap(int_address):
        store[lib.POINTER_RELATED_ERROR] = (MEMORY_RELATED_ERROR_TYPE.USE_AFTER_FREE, int_address)
    elif utils.MAX_HEAP_ADDR <= int_address:
        store[lib.POINTER_RELATED_ERROR] = (MEMORY_RELATED_ERROR_TYPE.UNINITIALIZED_CONTENT, int_address)
    elif int_address == 0:
        store[lib.POINTER_RELATED_ERROR] = (MEMORY_RELATED_ERROR_TYPE.NULL_POINTER_DEREFERENCE, int_address)


def read_memory_val(store, address, block_id, length=utils.MEM_ADDR_SIZE):
    res = None
    if sym_helper.is_bit_vec_num(address):
        val = None
        int_address = address.as_long()
        if sym_helper.addr_in_rodata_section(int_address):
            rodata_base_addr = global_var.binary_info.rodata_base_addr
            val = global_var.binary_content.read_bytes(int_address - rodata_base_addr, length // 8)
        elif sym_helper.addr_in_data_section(int_address):
            data_base_addr = global_var.binary_info.data_base_addr
            val = global_var.binary_content.read_bytes(int_address - data_base_addr, length // 8)
        elif sym_helper.addr_in_text_section(int_address):
            text_base_addr = global_var.binary_info.text_base_addr
            val = global_var.binary_content.read_bytes(int_address - text_base_addr, length // 8)
        else:
            read_mem_error_report(store, int_address)
        if val:
            res = BitVecVal(val, length)
        else:
            # Memory content that is dynamically allocated
            # It is not accessible statically
            res = BitVec(utils.MEM_DATA_SEC_SUFFIX + hex(int_address), length)
        store[lib.MEM][address] = [res, utils.INIT_BLOCK_NO]
    else:
        res = sym_helper.gen_mem_sym(length)
        store[lib.MEM][address] = [res, block_id]
    return res


def get_stdout_mem_val(store, address, length=utils.MEM_ADDR_SIZE):
    res = None
    tmp = is_mem_addr_in_stdout(store, address)
    if tmp is not None:
        res = get_mem_sym(store, tmp, length, lib.STDOUT)
        if res is None:
            res = sym_helper.gen_stdout_mem_sym(length)
            store[lib.STDOUT][tmp] = [res, utils.INIT_BLOCK_NO]
    return res


def get_memory_val(store, address, block_id, length=utils.MEM_ADDR_SIZE):
    res = get_stdout_mem_val(store, address, length)
    if res is None:
        res = get_mem_sym(store, address, length)
        if res == None:
            res = read_memory_val(store, address, block_id, length)
    return res


def get_mem_sym_block_id(store, address):
    res = None
    if address in store[lib.MEM]:
        res = store[lib.MEM][address][1]
    elif sym_helper.sym_is_int_or_bitvecnum(address):
        int_address = address.as_long()
        if sym_helper.addr_in_rodata_section(int_address): 
            res = utils.INIT_BLOCK_NO
        elif sym_helper.addr_in_data_section(int_address):
            res = store[lib.MEM_CONTENT_POLLUTED]
    else:
        res = store[lib.MEM_CONTENT_POLLUTED]
    return res


def get_seg_memory_val(store, address, seg, block_id, length=utils.MEM_ADDR_SIZE):
    res = None
    if address in store[seg]:
        res = store[seg][address]
    else:
        if sym_helper.is_bit_vec_num(address):
            int_address = address.as_long()
            res = BitVec(utils.MEM_DATA_SEC_SUFFIX + seg + ':' + hex(int_address), length)
        else:
            res = sym_helper.gen_mem_sym(length)
        store[seg][address] = res
    return res

