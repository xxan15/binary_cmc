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
from ..common import utils
from .sym_store import Sym_Store
from ..symbolic import sym_helper
from ..symbolic import sym_engine
from ..semantics import ext_handler
from ..semantics import smt_helper
from ..semantics import semantics


def gen_cjmp_idx_upperbound(inst_name, boundary):
    res = None
    jmp_condition = inst_name.split('j', 1)[1]
    if jmp_condition.startswith('n'):
        rest = jmp_condition.split('n')[1]
        if rest in utils.OPPOSITE_FLAG_MAP:
            jmp_condition = utils.OPPOSITE_FLAG_MAP[rest]
    if jmp_condition.startswith(('g', 'a')):
        if 'e' in jmp_condition:
            res = boundary
        else:
            res = boundary + 1
    return res


def gen_jt_idx_upperbound(trace_list, boundary):
    res = None
    idx = 0
    for idx, blk in enumerate(trace_list):
        inst = blk.inst
        if utils.check_not_single_branch_inst(inst):
            res = gen_cjmp_idx_upperbound(inst.split(' ', 1)[0], boundary)
            break
    return idx, res


def get_prev_address(address, address_inst_map):
    p_address = None
    for idx in range(1, utils.MAX_INST_ADDR_GAP):
        tmp = address - idx
        if tmp in address_inst_map:
            p_address = tmp
            break
    return p_address


def get_next_address(address, address_next_map, address_sym_table):
    next_address = address_next_map[address]
    if next_address in address_sym_table: return -1
    return next_address


def check_jt_assign_inst(inst_args):
    res = False
    inst_arg_s = inst_args.split(',')
    if len(inst_arg_s) == 2:
        inst_arg_0 = inst_arg_s[0].strip()
        inst_arg_1 = inst_arg_s[1].strip()
        if inst_arg_0 in lib.REG_NAMES and inst_arg_1.endswith(']') and 'rip' not in inst_arg_1:
            res = '*' in inst_arg_1 and '+' in inst_arg_1
    return res


def check_jump_table_assign_inst(trace_list, idx):
    res = False
    n_idx = 0
    for n_idx in range(idx+1, len(trace_list)):
        blk = trace_list[n_idx]
        inst = blk.inst
        if inst.startswith('mov'):
            res = check_jt_assign_inst(inst.split(' ', 1)[1].strip())
            if res: break
    return n_idx, res


# Read all the jump table entries
def get_distinct_jt_entries(blk, src_sym, jt_idx_upperbound, block_set):
    res = []
    inst = blk.inst
    inst_arg_split = inst.split(' ', 1)[1].strip().split(',')
    inst_dest = inst_arg_split[0]
    inst_src = inst_arg_split[1].strip()
    src_len = utils.get_sym_length(inst_src)
    parent_blk = block_set[blk.parent_id]
    p_store = parent_blk.sym_store.store
    for idx in range(jt_idx_upperbound):
        mem_address = sym_engine.get_jump_table_address(p_store, inst_src, src_sym, idx)
        mem_val = sym_engine.read_memory_val(p_store, mem_address, src_len)
        if not sym_helper.is_bit_vec_num(mem_val):
            return None, inst_dest, src_len
        if mem_val not in res:
            res.append(mem_val)
    return res, inst_dest, src_len


def detect_loop(block, address, new_address, block_set):
    exists_loop = False
    parent_id = block.parent_id
    prev_address = None
    while parent_id:
        parent_blk = block_set[parent_id]
        p_address = parent_blk.address
        if p_address == address:
            if prev_address and prev_address == new_address:
                exists_loop = True
                break
        parent_id = parent_blk.parent_id
        prev_address = p_address
    return exists_loop


def backtrack_to_start(block, address, block_set):
    trace_list = [address]
    parent_id = block.parent_id
    while parent_id:
        parent_blk = block_set[parent_id]
        p_address = parent_blk.address
        trace_list.append(p_address)
        parent_id = parent_blk.parent_id
    return trace_list


def reconstruct_jt_sym_stores(blk, distinct_entries, inst_dest, src_len):
    inst = blk.inst
    rip, store = blk.sym_store.rip, blk.sym_store.store
    dest_len = utils.get_sym_length(inst_dest)
    sym_store_list = []
    inst_name = inst.split(' ', 1)[0]
    for mem_val in distinct_entries:
        new_sym_store = Sym_Store(store, rip)
        if inst_name == 'mov':
            sym_engine.set_sym(new_sym_store.store, rip, inst_dest, mem_val)
        elif 's' in inst_name:
            semantics.mov_op(new_sym_store.store, inst_dest, dest_len, mem_val, src_len, True)
        elif 'z' in inst_name:
            semantics.mov_op(new_sym_store.store, inst_dest, dest_len, mem_val, src_len, False)
        sym_store_list.append(new_sym_store)
    return sym_store_list


def reconstruct_jt_target_addresses(trace_list, blk_idx, sym_store_list, address_jt_entries_map):
    for blk in trace_list[blk_idx + 1:]:
        address, inst, rip = blk.address, blk.inst, blk.sym_store.rip
        inst_split = inst.split(' ', 1)
        inst_name = inst_split[0]
        if utils.check_jmp_with_address(inst_name):
            inst_dest = inst_split[1].strip()
            target_addresses = []
            for sym_store in sym_store_list:
                target_addr = sym_engine.get_sym(sym_store.store, rip, inst_dest)
                target_addresses.append(target_addr)
            address_jt_entries_map[address] = (inst_dest, target_addresses)
            return inst_dest, target_addresses
        else:
            for sym_store in sym_store_list:
                sym_store.rip = rip
                semantics.parse_semantics(sym_store.store, rip, inst, blk.block_id)
    return None, None


def construct_print_info(parent_store, parent_rip, new_sym_store, rip, invariant_arguments):
    p_info = []
    stack_addr = []
    stack_top = sym_helper.top_stack_addr(new_sym_store.store)
    for inv_arg in invariant_arguments:
        if inv_arg in lib.REG_NAMES:
            p_info.append('register ' + inv_arg)
        else:
            p_info.append('memory address ' + inv_arg)
            if utils.imm_start_pat.match(inv_arg):
                mem_addr = utils.imm_str_to_int(inv_arg)
                if mem_addr >= stack_top:
                    stack_addr.append(inv_arg)
        prev_val = sym_engine.get_sym(parent_store, parent_rip, inv_arg)
        sym_engine.set_sym(new_sym_store.store, rip, inv_arg, prev_val)
    print_info = ', '.join(p_info)
    return print_info, stack_addr


def get_inv_arg_val(store, rip, inv_arg, length=lib.DEFAULT_REG_LEN):
    res = None
    if inv_arg in lib.REG_NAMES:
        res = sym_engine.get_sym(store, rip, inv_arg, length)
    else:
        res = sym_engine.get_sym(store, rip, '[' + inv_arg + ']', length)
    return res


def substitute_inv_arg_val_direct(store, rip, inv_arg, inv_val):
    if inv_arg in lib.REG_NAMES:
        sym_engine.set_sym(store, rip, inv_arg, inv_val)
    else:
        sym_engine.set_sym(store, rip, '[' + inv_arg + ']', inv_val)


def substitute_sym_arg_for_all(store, sym_arg, sym_new):
    for name in lib.RECORD_STATE_NAMES:
        s = store[name]
        for k, v in s.items():
            s[k] = sym_helper.substitute_sym_val(v, sym_arg, sym_new)


def retrieve_call_inst_func_name(func_call_blk, address_inst_map, address_sym_table):
    func_name = None
    rip, store = func_call_blk.sym_store.rip, func_call_blk.sym_store.store
    jump_address_str = func_call_blk.inst.split(' ', 1)[1].strip()
    new_address = smt_helper.get_jump_address(store, rip, jump_address_str)
    if new_address in address_inst_map:
        func_name = get_function_name_from_addr_sym_table(address_sym_table, new_address)
    elif new_address in address_sym_table:
        func_name = get_function_name_from_addr_sym_table(address_sym_table, new_address)
    return func_name, new_address


def cfg_init_parameter(store, sym_table):
    if lib.STDOUT in sym_table:
        stdout_address = sym_table[lib.STDOUT]
        sym_address = sym_helper.bit_vec_val_sym(stdout_address)
        store[lib.STDOUT_ADDRESS] = sym_address
        store[lib.STDOUT_HANDLER] = sym_engine.get_memory_val(store, sym_address)


def retrieve_internal_call_inst_func_name(func_call_blk, address_inst_map, address_sym_table):
    func_name = None
    rip, store = func_call_blk.sym_store.rip, func_call_blk.sym_store.store
    jump_address_str = func_call_blk.inst.split(' ', 1)[1].strip()
    new_address = smt_helper.get_jump_address(store, rip, jump_address_str)
    if new_address in address_inst_map or new_address in address_sym_table:
        func_name = get_function_name_from_addr_sym_table(address_sym_table, new_address)
    return func_name, new_address


def check_path_reachability(constraint):
    res = True
    predicates = constraint.get_predicates()
    res = sym_helper.check_pred_satisfiable(predicates)
    return res


def check_unsatisfied_input(constraint):
    res = True
    predicates = constraint.get_predicates()
    unsat_predicates = [sym_helper.sym_not(p) for p in predicates]
    res = sym_helper.check_pred_satisfiable(unsat_predicates)
    return res


def find_out_func_name_with_addr_in_range(func_start_addr_name_map, address):
    res = ''
    start_addr_list = list(func_start_addr_name_map.keys())
    start_addr_list.sort()
    addr_num = len(start_addr_list)
    for idx, start_addr in enumerate(start_addr_list):
        if idx + 1 < addr_num:
            next_addr = start_addr_list[idx + 1]
            if address >= start_addr and address < next_addr:
                res = func_start_addr_name_map[start_addr]
                break
        else:
            res = func_start_addr_name_map[start_addr]
    return res


def collect_statistic_data_from_map(cmc_func_exec_info):
    res = [0] * utils.CMC_EXEC_RES_COUNT
    for name in cmc_func_exec_info:
        func_exec_info = cmc_func_exec_info[name]
        if res:
            for idx, _ in enumerate(res):
                res[idx] += func_exec_info[idx]
        else:
            res = func_exec_info
    return res


def get_function_name_from_addr_sym_table(address_sym_table, address):
    res = ''
    if address in address_sym_table:
        val = address_sym_table[address]
        if len(val) > 1:
            res = val[1]
        else:
            res = val[0]
    return res
 

def start_init(store, rip, block_id):
    dests = lib.REG64_NAMES
    ext_handler.set_regs_sym(store, rip, dests, block_id)
    sym_engine.set_sym(store, rip, 'rsp', sym_helper.bit_vec_val_sym(utils.INIT_STACK_FRAME_POINTER), block_id)
    ext_handler.set_segment_regs_sym(store, rip)
    # utils.logger.debug('The following registers are set to symbolic value: ' + str(dests))
    ext_handler.clear_flags(store)
    sym_src = sym_helper.gen_sym()
    sym_rsp = sym_engine.get_sym(store, rip, 'rsp', block_id)
    sym_engine.set_mem_sym(store, sym_rsp, sym_src, block_id)
    
