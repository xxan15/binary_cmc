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

from ..common import lib
from ..common.lib import TRACE_BACK_TYPE
from ..common import utils
from ..symbolic import sym_engine
from ..symbolic import sym_helper
from . import smt_helper
from . import semantics

rip = 0
func_call_point, halt_point, mem_len_map = False, False, {}


def sym_bin_on_src(store, sym_names, src):
    global mem_len_map
    src_names = sym_names
    src_len = utils.get_sym_length(src)
    sym_src = sym_engine.get_sym(store, rip, src, utils.TB_DEFAULT_BLOCK_NO, src_len)
    if not sym_helper.sym_is_int_or_bitvecnum(sym_src):
        if ':' in src:
            lhs, rhs = src.split(':')
            src_names = smt_helper.add_src_to_syms(store, sym_names, lhs)
            src_names = smt_helper.add_src_to_syms(store, src_names, rhs)
        elif src.endswith(']'):
            new_srcs, is_reg_bottom = smt_helper.get_bottom_source(src, store, rip, mem_len_map)
            if is_reg_bottom:
                src_names = src_names + new_srcs
            else:
                addr = sym_engine.get_effective_address(store, rip, src)
                src_names = src_names + [str(addr)]
                length = utils.get_sym_length(src)
                mem_len_map[str(addr)] = length
            # src_names = src_names + new_srcs
        else:
            src_names.append(smt_helper.get_root_reg(src))
    else:
        if ':' in src:
            lhs, rhs = src.split(':')
            smt_helper.remove_reg_from_sym_srcs(lhs, src_names)
            smt_helper.remove_reg_from_sym_srcs(rhs, src_names)
        elif src.endswith(']'):
            new_srcs = smt_helper.get_mem_reg_source(src)
            src_names = list(set(src_names) - set(new_srcs))
        else:
            smt_helper.remove_reg_from_sym_srcs(src, src_names)
    return list(set(src_names))


def sym_bin_op(store, sym_names, dest, src1, src2=None):
    src_names = sym_names
    if smt_helper.check_source_is_sym(store, rip, dest, sym_names):
        src2 = dest if src2 == None else src2
        src_names = sym_bin_on_src(store, sym_names, src1)
        src_names = sym_bin_on_src(store, src_names, src2)
    return list(set(src_names))


def mov_op(store, sym_names, dest, src):
    global mem_len_map
    src_names = sym_names
    if smt_helper.check_source_is_sym(store, rip, dest, sym_names):
        if src in lib.REG_NAMES:
            if dest.endswith(']'):
                addr = sym_engine.get_effective_address(store, rip, dest)
                dest_reg = str(addr)
            else:
                dest_reg = smt_helper.get_root_reg(dest)
            if dest_reg in src_names:
                src_names.remove(dest_reg)
            # remove_reg_from_sym_srcs(dest, src_names)
            src_names.append(smt_helper.get_root_reg(src))
            # return list(set(src_names))
            # src_names = smt_helper.add_new_reg_src(sym_names, dest, src)
        elif src.endswith(']'):
            smt_helper.remove_reg_from_sym_srcs(dest, src_names)
            new_srcs, is_reg_bottom = smt_helper.get_bottom_source(src, store, rip, mem_len_map)
            if is_reg_bottom:
                src_names = src_names + new_srcs
            else:
                addr = sym_engine.get_effective_address(store, rip, src)
                src_names = src_names + [str(addr)]
                length = utils.get_sym_length(src)
                mem_len_map[str(addr)] = length
    return list(set(src_names))


def mov(store, sym_names, dest, src):
    global mem_len_map, halt_point
    src_names = sym_names
    if smt_helper.check_source_is_sym(store, rip, dest, sym_names):
        if src in lib.REG_NAMES:
            if dest.endswith(']'):
                addr = sym_engine.get_effective_address(store, rip, dest)
                dest_reg = str(addr)
            else:
                dest_reg = smt_helper.get_root_reg(dest)
            if dest_reg in src_names:
                src_names.remove(dest_reg)
            # remove_reg_from_sym_srcs(dest, src_names)
            src_names.append(smt_helper.get_root_reg(src))
            # return list(set(src_names))
            # src_names = smt_helper.add_new_reg_src(sym_names, dest, src)
        elif src.endswith(']'):
            smt_helper.remove_reg_from_sym_srcs(dest, src_names)
            new_srcs, is_reg_bottom = smt_helper.get_bottom_source(src, store, rip, mem_len_map)
            if is_reg_bottom:
                src_names = src_names + new_srcs
            else:
                addr = sym_engine.get_effective_address(store, rip, src)
                src_names = src_names + [str(addr)]
                length = utils.get_sym_length(src)
                mem_len_map[str(addr)] = length
                if str(addr) not in store[lib.MEM]: halt_point = True
    return list(set(src_names))


def lea(store, sym_names, dest, src):
    global mem_len_map
    src_names = sym_names
    dest_root = smt_helper.get_root_reg(dest)
    if dest_root in src_names:
        src_names.remove(dest_root)
        # addr = sym_engine.get_effective_address(store, rip, src)
        # if sym_helper.sym_is_int_or_bitvecnum(addr):
        #     pass
        # else:
        new_srcs, _ = smt_helper.get_bottom_source(src, store, rip, mem_len_map)
        src_names = src_names + new_srcs
    return list(set(src_names))


def push(store, sym_names, src):
    src_names = sym_names
    sym_rsp = sym_engine.get_sym(store, rip, 'rsp', utils.TB_DEFAULT_BLOCK_NO)
    prev_rsp = str(sym_helper.sym_op('-', sym_rsp, utils.MEM_ADDR_SIZE // 8))
    if prev_rsp in sym_names:
        src_names.remove(prev_rsp)
    src_names.append(smt_helper.get_root_reg(src))
    return src_names

def pop(store, sym_names, dest):
    sym_rsp = str(sym_engine.get_sym(store, rip, 'rsp', utils.TB_DEFAULT_BLOCK_NO))
    src_names = sym_names
    smt_helper.remove_reg_from_sym_srcs(dest, src_names)
    new_srcs = [sym_rsp]
    src_names = src_names + new_srcs
    mem_len_map[sym_rsp] = utils.MEM_ADDR_SIZE
    return src_names


def xchg(store, sym_names, dest, src):
    src_names = sym_names
    if smt_helper.check_source_is_sym(store, rip, dest, sym_names):
        src_names = smt_helper.add_new_reg_src(sym_names, dest, src)
    return src_names


def mul_op(store, sym_names, src):
    src_names = sym_names
    bits_len = utils.get_sym_length(src)
    a_reg, _, dest = lib.AUX_REG_INFO[bits_len]
    src_names = sym_bin_op(store, sym_names, dest, a_reg, src)
    return src_names


def imul(store, sym_names, dest, src1=None, src2=None):
    src_names = sym_names
    if src1 != None:
        if src2 == None:
            src_names = sym_bin_op(store, sym_names, dest, src1)
        else:
            src_names = sym_bin_op(store, sym_names, src1, src2)
    else:
        src_names = mul_op(store, sym_names, dest)
    return src_names


def div_op(store, sym_names, src):
    bits_len = utils.get_sym_length(src)
    qreg, rreg, dest = lib.AUX_REG_INFO[bits_len]
    src_names = sym_bin_op(store, sym_names, qreg + ':' +rreg, dest, src)
    return src_names


def cdqe(store, sym_names):
    return sym_names


def cmpxchg(store, sym_names, dest, src):
    src_names = sym_names
    bits_len = utils.get_sym_length(dest)
    a_reg = lib.AUX_REG_INFO[bits_len][0]
    sym_lhs = sym_engine.get_sym(store, rip, a_reg, utils.TB_DEFAULT_BLOCK_NO, bits_len)
    sym_rhs = sym_engine.get_sym(store, rip, dest, utils.TB_DEFAULT_BLOCK_NO, bits_len)
    eq = sym_helper.is_equal(sym_lhs, sym_rhs)
    if eq == True:
        src_names = mov_op(store, sym_names, dest, src)
    else:
        src_names = mov_op(store, sym_names, a_reg, dest)
    return src_names
    

def cmov(store, sym_names, inst, dest, src):
    src_names = sym_names
    res = smt_helper.parse_predicate(store, inst, True, 'cmov')
    if res == False: pass
    else: src_names = mov_op(store, sym_names, dest, src)
    return src_names


def jmp_op(sym_names):
    sym_in_stack = []
    rest = []
    for sym in sym_names:
        res = smt_helper.check_sym_is_stack_addr(sym)
        if res:
            sym_in_stack.append(sym)
        else:
            rest.append(sym)
    return sym_in_stack, rest


def call(store, sym_names):
    sym_in_stack, sym_not_in_stack = jmp_op(sym_names)
    func_call_point = True
    for sym_name in sym_not_in_stack:
        length = utils.MEM_ADDR_SIZE
        if sym_name not in lib.REG_NAMES:
            length = mem_len_map[sym_name]
        if utils.imm_start_pat.match(sym_name):
            sym_name = '[' + sym_name + ']'
            val = sym_engine.get_sym(store, rip, sym_name, utils.TB_DEFAULT_BLOCK_NO, length)
            if sym_helper.is_bv_sym_var(val):
                func_call_point = False
    return func_call_point


def jmp_to_external_func(store, sym_names):
    sym_in_stack, sym_not_in_stack = jmp_op(sym_names)
    func_call_point = True
    for sym_name in sym_not_in_stack:
        length = utils.MEM_ADDR_SIZE
        if sym_name not in lib.REG_NAMES:
            length = mem_len_map[sym_name]
        if utils.imm_start_pat.match(sym_name):
            sym_name = '[' + sym_name + ']'
            val = sym_engine.get_sym(store, rip, sym_name, utils.TB_DEFAULT_BLOCK_NO, length)
            if sym_helper.is_bv_sym_var(val):
                func_call_point = False
        elif sym_name in lib.REG64_NAMES:
            if sym_name not in lib.CALLEE_NOT_SAVED_REGS:
                func_call_point = False
    return func_call_point


INSTRUCTION_SEMANTICS_MAP = {
    'mov': mov,
    'lea': lea,
    'push': push,
    'pop': pop,
    'add': sym_bin_op,
    'sub': sym_bin_op,
    'xor': sym_bin_op,
    'and': sym_bin_op,
    'or': sym_bin_op,
    'sar': sym_bin_op,
    'shr': sym_bin_op,
    'sal': sym_bin_op,
    'shl': sym_bin_op,
    'xchg': xchg,
    'imul': imul,
    'mul': mul_op,
    'idiv': div_op,
    'div': div_op,
    'cmpxchg': cmpxchg,
    'movzx': mov,
    'movsx': mov,
    'movsxd': mov,
    'adc': sym_bin_op,
    'sbb': sym_bin_op,
    'cdqe': cdqe
}


def parse_sym_src(address_ext_func_map, dll_func_info, address_inst_map, store, curr_rip, inst, sym_names):
    global rip, func_call_point, halt_point, mem_len_map
    rip = curr_rip
    func_call_point, halt_point = False, False
    if inst.startswith('lock '):
        inst = inst.split(' ', 1)[1]
    inst_split = inst.strip().split(' ', 1)
    inst_name = inst_split[0]
    src_names = sym_names
    if inst_name in INSTRUCTION_SEMANTICS_MAP:
        inst_op = INSTRUCTION_SEMANTICS_MAP[inst_name]
        inst_args = utils.parse_inst_args(inst_split)
        src_names = inst_op(store, sym_names, *inst_args)
    elif inst_name in ('nop', 'hlt'): pass
    elif inst_name.startswith('cmov'):
        inst_args = utils.parse_inst_args(inst_split)
        src_names = cmov(store, sym_names, inst, *inst_args)
    elif inst_name.startswith('rep'):
        inst = inst_split[1].strip()
        src_names, func_call_point, halt_point, mem_len_map = parse_sym_src(address_ext_func_map, dll_func_info, address_inst_map, store, curr_rip, inst, sym_names)
    elif utils.check_jmp_with_address(inst):
        jump_address_str = inst.split(' ', 1)[1].strip()
        new_address = smt_helper.get_jump_address(store, rip, jump_address_str)
        if new_address in address_ext_func_map or new_address in dll_func_info:
            func_call_point = jmp_to_external_func(store, sym_names)
    return src_names, func_call_point, halt_point, mem_len_map

