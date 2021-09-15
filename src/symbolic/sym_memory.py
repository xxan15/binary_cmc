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
from z3 import *
from ..common import lib
from ..common import utils
from . import sym_helper
from ..common import global_var
from ..common.lib import MEM_DATA_SECT_STATUS
from ..common.lib import MEMORY_RELATED_ERROR_TYPE

letter_num_neg_pat = re.compile(r'\w+')
sym_pat = re.compile(r'\W+')

def get_sym_val(str_val, store, length):
    res = None
    if str_val in lib.REG_NAMES:
        res = store[lib.REG][str_val]
    elif utils.imm_pat.match(str_val):
        res = BitVecVal(utils.imm_str_to_int(str_val), length)
    elif str_val in lib.SEG_REGS:
        res = store[str_val][str_val]
    else:
        res = BitVec(str_val, length)
    return res

def get_idx_sym_val(store, arg, src_sym, src_val, length):
    res = None
    if arg in lib.REG_NAMES:
        res = store[lib.REG][arg]
        if not sym_helper.is_bit_vec_num(res):
            m = sym_helper.check_pred_satisfiable([src_sym == src_val])
            if m is not False:
                for d in m.decls():
                    s_val = m[d]
                    s_len = s_val.size()
                    res = substitute(res, (BitVec(d.name(), s_len), s_val))
                res = simplify(res)
            # else:
            #     utils.logger.info('Failed to solve the equation ' + str(src_sym) + ' == ' + str(src_val))
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
    # line_split = re.split(r'(\W+)', line)
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
    # for lsi in line_split:
    #     lsi = lsi.strip()
    #     if re.match(r'\w+|-\w+', lsi):
    #         val = get_sym_val(lsi, store, length)
    #         stack.append(val)
    #     else:
    #         op_stack.append(lsi)
    res = eval_simple_formula(stack, op_stack)
    return res


# arg: DWORD PTR [rcx+rdx*4]
def get_jump_table_address(store, arg, src_sym, src_val, length=lib.DEFAULT_REG_LEN):
    arg = utils.extract_content(arg, '[')
    # arg_split = re.split(r'(\W+)', arg)
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
    # for ai in arg_split:
    #     ai = ai.strip()
    #     if re.match(r'\w+|-\w+', ai):
    #         val = get_idx_sym_val(store, ai, src_sym, src_val, length)
    #         stack.append(val)
    #     else:
    #         op_stack.append(ai)
    res = eval_simple_formula(stack, op_stack)
    return res


def get_effective_address(store, rip, src, length=lib.DEFAULT_REG_LEN):
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


def reset_mem_content_pollute(store):
    store[lib.MEM_CONTENT_POLLUTED] = MEM_DATA_SECT_STATUS.RESTORED


def pollute_all_mem_content(store):
    store[lib.MEM_CONTENT_POLLUTED] = MEM_DATA_SECT_STATUS.POLLUTED
    addr_list = list(store[lib.MEM].keys())
    for addr in addr_list:
        if not sym_helper.sym_is_int_or_bitvecnum(addr):
            if sym_helper.sym_is_int_or_bitvecnum(store[lib.MEM][addr]):
                store[lib.MEM][addr] = sym_helper.gen_sym(store[lib.MEM][addr].size())
        else:
            int_addr = sym_helper.int_from_sym(addr)
            if int_addr >= global_var.elf_info.data_start_addr and int_addr < utils.MAX_HEAP_ADDR:
                if sym_helper.sym_is_int_or_bitvecnum(store[lib.MEM][addr]):
                    store[lib.MEM][addr] = sym_helper.gen_sym(store[lib.MEM][addr].size())


def pollute_mem_w_sym_address(store):
    for addr in store[lib.MEM]:
        if not sym_helper.sym_is_int_or_bitvecnum(addr):
            if sym_helper.sym_is_int_or_bitvecnum(store[lib.MEM][addr]):
                store[lib.MEM][addr] = sym_helper.gen_sym(store[lib.MEM][addr].size())


def addr_in_rodata_section(int_addr):
    return global_var.elf_info.rodata_start_addr <= int_addr < global_var.elf_info.rodata_end_addr


def addr_in_data_section(int_addr):
    return global_var.elf_info.data_start_addr <= int_addr < global_var.elf_info.data_end_addr


def addr_in_heap(int_addr):
    return utils.MIN_HEAP_ADDR <= int_addr < utils.MAX_HEAP_ADDR

    
def check_buffer_overflow(store, address, length):
    byte_len = length // 8
    int_address = address.as_long()
    stack_top = sym_helper.top_stack_addr(store)
    if addr_in_data_section(int_address) or addr_in_heap(int_address):
        if address in store[lib.MEM]:
            prev_sym = store[lib.MEM][address]
            prev_len = prev_sym.size() // 8
            # if byte_len > prev_len:
            #     utils.output_logger.error('Error: Potential buffer overflow at address ' + hex(int_address))
            #     store[lib.POINTER_RELATED_ERROR] = True
        for offset in range(-7, byte_len):
            if offset != 0:
                curr_address = simplify(address + offset)
                if curr_address in store[lib.MEM]:
                    prev_sym = store[lib.MEM][curr_address]
                    prev_len = prev_sym.size() // 8
                    if (offset < 0 and prev_len > -offset) or offset > 0:
                        utils.output_logger.error('Error: Potential buffer overflow at address ' + hex(int_address) + '\n')
                        store[lib.POINTER_RELATED_ERROR] = MEMORY_RELATED_ERROR_TYPE.BUFFER_OVERFLOW
    elif stack_top and utils.MAX_HEAP_ADDR <= int_address < stack_top:
        utils.output_logger.error('Error: Buffer overflow at address ' + hex(int_address) + '\n')
        store[lib.POINTER_RELATED_ERROR] = MEMORY_RELATED_ERROR_TYPE.BUFFER_OVERFLOW


def set_mem_sym_val(store, address, sym, length=lib.DEFAULT_REG_LEN, store_key=lib.MEM): 
    byte_len = length // 8
    if address in store[store_key]:
        prev_sym = store[store_key][address]
        prev_len = prev_sym.size() // 8
        if byte_len < prev_len:
            curr_address = simplify(address + byte_len)
            store[store_key][curr_address] = simplify(sym_helper.extract_bytes(prev_len, byte_len, prev_sym))
    store[store_key][address] = sym
    for offset in range(-7, byte_len):
        if offset != 0:
            curr_address = simplify(address + offset)
            if curr_address in store[store_key]:
                prev_sym = store[store_key][curr_address]
                prev_len = prev_sym.size() // 8
                if offset < 0 and prev_len > -offset:
                    store[store_key][curr_address] = simplify(sym_helper.extract_bytes(-offset, 0, prev_sym))
                elif offset > 0:
                    sym_helper.remove_memory_content(store, curr_address)
                    if prev_len - byte_len + offset > 0:
                        new_address = simplify(address + byte_len)
                        new_sym = simplify(sym_helper.extract_bytes(prev_len, byte_len - offset, prev_sym))
                        store[store_key][new_address] = new_sym
                        break  


def is_mem_addr_in_stdout(store, address):
    res = None
    if lib.STDOUT_HANDLER in store:
        stdout_handler = store[lib.STDOUT_HANDLER]
        tmp = simplify(address - stdout_handler)
        if sym_helper.is_bit_vec_num(tmp):
            res = tmp
        else:
            # utils.logger.info('is_mem_addr_in_stdout')
            # utils.logger.info(address)
            stdout = BitVec('stdout', lib.DEFAULT_REG_LEN)
            tmp = simplify(address - stdout)
            if sym_helper.is_bit_vec_num(tmp):
                res = address
    return res

def set_mem_sym(store, address, sym, length=lib.DEFAULT_REG_LEN):
    # If the memory address is not concrete
    if not sym_helper.sym_is_int_or_bitvecnum(address):
        tmp = is_mem_addr_in_stdout(store, address)
        if tmp is not None:
            set_mem_sym_val(store, tmp, sym, length, lib.STDOUT)
        else:
            pollute_all_mem_content(store)
            store[lib.MEM][address] = sym
            utils.logger.error('Error: Potential buffer overflow with symbolic memory address\n')
            return -2
    else:
        check_buffer_overflow(store, address, length)
        set_mem_sym_val(store, address, sym, length)
        pollute_mem_w_sym_address(store)
    return 0

            
    
def get_mem_sym(store, address, length=lib.DEFAULT_REG_LEN, store_key=lib.MEM):
    byte_len = length // 8
    res = None
    start_address = None
    for offset in range(8):
        curr_address = simplify(address - offset)
        if curr_address in store[store_key]:
            start_address = curr_address
            break
    if start_address is not None:
        sym = store[store_key][start_address]
        sym_len = sym.size() // 8
        if sym_len > offset:
            right_bound = min(sym_len, byte_len + offset)
            first_sym = sym_helper.extract_bytes(right_bound, offset, sym)
            if right_bound - offset < byte_len:
                temp = [first_sym]
                tmp_len = right_bound - offset
                while tmp_len < byte_len:
                    next_address = simplify(address + tmp_len)
                    if next_address in store[store_key]:
                        next_sym = store[store_key][next_address]
                        next_len = next_sym.size() // 8
                        r_bound = min(next_len, byte_len - tmp_len)
                        curr = sym_helper.extract_bytes(r_bound, 0, next_sym)
                        temp.append(curr)
                        tmp_len += r_bound
                    else:
                        break
                if tmp_len == byte_len:
                    temp.reverse()
                    res = simplify(Concat(temp))
            else:
                res = simplify(first_sym)
    return res


def read_memory_val(store, address, length=lib.DEFAULT_REG_LEN):
    res = None
    if sym_helper.is_bit_vec_num(address):
        val = None
        int_address = address.as_long()
        # if int_address in global_var.elf_info.sym_mem_info_table:
        #     val = global_var.elf_info.sym_mem_info_table[int_address]
        if addr_in_rodata_section(int_address):
            rodata_base_addr = global_var.elf_info.rodata_base_addr
            val = global_var.elf_content.read_bytes(int_address - rodata_base_addr, length // 8)
        elif store[lib.MEM_CONTENT_POLLUTED]==MEM_DATA_SECT_STATUS.RAW and addr_in_data_section(int_address):
            data_base_addr = global_var.elf_info.data_base_addr
            val = global_var.elf_content.read_bytes(int_address - data_base_addr, length // 8)
        else:
            if addr_in_heap(int_address):
                utils.output_logger.error('Error: Use after free at address ' + hex(int_address) + '\n')
                store[lib.POINTER_RELATED_ERROR] = MEMORY_RELATED_ERROR_TYPE.USE_AFTER_FREE
            elif int_address >= utils.MAX_HEAP_ADDR:
                utils.output_logger.error('Error: Null pointer dereference at address ' + hex(int_address) + '\n')
                store[lib.POINTER_RELATED_ERROR] = MEMORY_RELATED_ERROR_TYPE.NULL_POINTER_DEREFERENCE
        if val:
            res = BitVecVal(val, length)
        else:
            # res = BitVecVal(0, length)
            res = BitVec(utils.MEM_DATA_SEC_SUFFIX + hex(int_address), length)
        store[lib.MEM][address] = res
        # pollute_mem_w_sym_address(store)
    else:
        # pollute_all_mem_content(store)
        res = sym_helper.gen_mem_sym(length)
        store[lib.MEM][address] = res
    return res


def get_stdout_mem_val(store, address, length=lib.DEFAULT_REG_LEN):
    res = None
    tmp = is_mem_addr_in_stdout(store, address)
    if tmp is not None:
        res = get_mem_sym(store, tmp, length, lib.STDOUT)
        if res is None:
            res = sym_helper.gen_stdout_mem_sym(length)
            store[lib.STDOUT][tmp] = res
    return res


def get_memory_val(store, address, length=lib.DEFAULT_REG_LEN):
    res = get_stdout_mem_val(store, address, length)
    if res is None:
        res = get_mem_sym(store, address, length)
        if res == None:
            res = read_memory_val(store, address, length)
    return res


def get_seg_memory_val(store, address, seg, length=lib.DEFAULT_REG_LEN):
    res = None
    if address in store[seg]:
        res = store[seg][address]
    else:
        res = sym_helper.gen_mem_sym(length)
        store[seg][address] = res
    return res

