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
import random
from z3 import *

from ..common import lib
from ..common import utils
from .constraint import Constraint
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
        mem_val = sym_engine.read_memory_val(p_store, mem_address, utils.INIT_BLOCK_NO, src_len)
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
        if parent_id in block_set:
            parent_blk = block_set[parent_id]
            p_address = parent_blk.address
            if p_address == address:
                if prev_address and prev_address == new_address:
                    exists_loop = True
                    break
            parent_id = parent_blk.parent_id
            prev_address = p_address
        else: break
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
                target_addr = sym_engine.get_sym(sym_store.store, rip, inst_dest, utils.INIT_BLOCK_NO)
                target_addresses.append(target_addr)
            address_jt_entries_map[address] = (inst_dest, target_addresses)
            return inst_dest, target_addresses
        else:
            for sym_store in sym_store_list:
                sym_store.rip = rip
                semantics.parse_semantics(sym_store.store, rip, inst, blk.block_id)
    return None, None


def get_unified_sym_name(address_sym_table, address):
    res = ''
    if address in address_sym_table:
        sym_name = address_sym_table[address][0]
        res = sym_name.split('@', 1)[0].strip()
    return res


def get_real_length(mem_len_map, arg):
    length = lib.DEFAULT_REG_LEN
    if arg not in lib.REG_NAMES:
        length = mem_len_map[arg]
    return length

def construct_print_info(parent_id, parent_store, parent_rip, new_sym_store, rip, invariant_arguments):
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
        prev_val = sym_engine.get_sym(parent_store, parent_rip, inv_arg, parent_id)
        sym_engine.set_sym(new_sym_store.store, rip, inv_arg, prev_val)
    print_info = ', '.join(p_info)
    return print_info, stack_addr


def get_inv_arg_val(store, rip, inv_arg, block_id, length=lib.DEFAULT_REG_LEN):
    res = None
    if inv_arg in lib.REG_NAMES:
        res = sym_engine.get_sym(store, rip, inv_arg, block_id, length)
    else:
        res = sym_engine.get_sym(store, rip, '[' + inv_arg + ']', block_id, length)
    return res
    

def repeated_random_concretization(conc_res, sym_val, sym_len, count):
    while len(conc_res[sym_val]) < count:
        # rand_val = random.randint(0, 2**sym_len - 1)
        rand_val = random.randint(0, utils.MAX_ARGC_NUM)
        if sym_val not in conc_res:
            conc_res[sym_val] = [sym_helper.bit_vec_val_sym(rand_val, sym_len)]
        else:
            conc_res[sym_val].append(sym_helper.bit_vec_val_sym(rand_val, sym_len))



def ramdom_concretize_sym(conc_res, sym_vals, sym_lens, count):
    for idx, sym_val in enumerate(sym_vals):
        sym_len = sym_lens[idx]
        if sym_val in conc_res:
            repeated_random_concretization(conc_res, sym_val, sym_len, count)
        else:
            # rand_val = random.randint(0, 2**sym_len - 1)
            rand_val = random.randint(0, utils.MAX_ARGC_NUM)
            conc_res[sym_val] = [sym_helper.bit_vec_val_sym(rand_val, sym_len)]
            repeated_random_concretization(conc_res, sym_val, sym_len, count)

            

def concretize_sym_arg(sym_vals, sym_lens, constraint):
    conc_res = {}
    random.seed()
    sym_val_strs = [str(sym_val) for sym_val in sym_vals]
    sym_exist_in_constraint = False
    predicates = constraint.get_predicates()
    m_list = sym_helper.repeated_check_pred_satisfiable(predicates, utils.REBUILD_BRANCHES_NUM)
    if m_list:
        for m in m_list:
            for d in m.decls():
                d_name = d.name()
                if d_name in sym_val_strs:
                    sym_exist_in_constraint = True
                    idx = sym_val_strs.index(d_name)
                    sym_val = sym_vals[idx]
                    if sym_val in conc_res:
                        conc_res[sym_val].append(m[d])
                    else:
                        conc_res[sym_val] = [m[d]]
            if not sym_exist_in_constraint: break
    ramdom_concretize_sym(conc_res, sym_vals, sym_lens, utils.REBUILD_BRANCHES_NUM)
    return conc_res


def update_sym_addr_valueset_map(sym_addr_valueset_map, concretize_sym_args):
    for sym_val in concretize_sym_args:
        if sym_val not in sym_addr_valueset_map:
            sym_addr_valueset_map[sym_val] = concretize_sym_args[sym_val]
        # if sym_val not in sym_addr_valueset_map:
        #     sym_addr_valueset_map[sym_val] = conc_vals
        # else:
        #     sym_addr_valueset_map[sym_val].append(conc_val)


def resolve_value_for_stack_addr_inv_arg(self, block_id, sym_store, stack_addr, substitute_pair, last_constraint):
    predicates = last_constraint.get_predicates()
    m = sym_helper.check_pred_satisfiable(predicates)
    if m is not False:
        stack_val_len = self.mem_len_map[stack_addr]
        stack_val = sym_engine.get_sym(sym_store.store, sym_store.rip, '[' + stack_addr + ']', block_id, stack_val_len)
        res = stack_val
        for d in m.decls():
            s_val = m[d]
            s_len = s_val.size()
            res = sym_helper.substitute_sym_val(res, sym_helper.bit_vec_wrap(d.name(), s_len), s_val)
            substitute_pair.append((sym_helper.bit_vec_wrap(d.name(), s_len), s_val))
        sym_engine.set_sym(sym_store.store, sym_store.rip, '[' + stack_addr + ']', res)


def substitute_inv_arg_val_direct(store, rip, inv_arg, inv_val):
    if inv_arg in lib.REG_NAMES:
        sym_engine.set_sym(store, rip, inv_arg, inv_val)
    else:
        sym_engine.set_sym(store, rip, '[' + inv_arg + ']', inv_val)


def substitute_sym_arg_for_all(store, sym_arg, sym_new):
    for name in lib.RECORD_STATE_NAMES:
        s = store[name]
        for k, v in s.items():
            s[k][0] = sym_helper.substitute_sym_val(v[0], sym_arg, sym_new)
            

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
    if lib.STDIN in sym_table:
        stdin_address = sym_table[lib.STDIN]
        sym_address = sym_helper.bit_vec_val_sym(stdin_address)
        store[lib.STDIN_ADDRESS] = sym_address
        store[lib.STDIN_HANDLER] = sym_engine.get_memory_val(store, sym_address, utils.INIT_BLOCK_NO)
    if lib.STDOUT in sym_table:
        stdout_address = sym_table[lib.STDOUT]
        sym_address = sym_helper.bit_vec_val_sym(stdout_address)
        store[lib.STDOUT_ADDRESS] = sym_address
        store[lib.STDOUT_HANDLER] = sym_engine.get_memory_val(store, sym_address, utils.INIT_BLOCK_NO)


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
    

def get_sym_val(store, rip, src, block_id):
    res = None
    src = src.strip()
    res = sym_engine.get_sym(store, rip, src, block_id)
    return res


def preprocess_constraint(store, rip, block_id, ext_name, constraint):
    res = None
    if 'fresh heap pointer' in constraint:
        # op = re.search(r'[<!=>]+', constraint).group(0)
        # arg = constraint.split(op, 1)[0].strip()
        # res = utils.MIN_HEAP_ADDR + '<=' + arg + '<=' + utils.MAX_HEAP_ADDR
        # mem_size = sym_engine.get_sym(store, rip, 'rdi', block_id) if ext_name in ('malloc', 'calloc') else sym_engine.get_sym(store, rip, 'rsi', block_id)
        mem_size = sym_helper.bit_vec_val_sym(utils.MAX_MALLOC_SIZE)
        ext_handler.ext_gen_fresh_heap_pointer(store, rip, ext_name, block_id, mem_size)
    else:
        res = constraint
    return res


def parse_basic_pred(store, rip, block_id, logic_op, lhs, rhs):
    lhs = get_sym_val(store, rip, lhs, block_id)
    rhs = get_sym_val(store, rip, rhs, block_id)
    if lhs == None or rhs == None: return None
    pred = sym_helper.LOGIC_OP_FUNC_MAP[logic_op](lhs, rhs)
    return pred


def parse_single_predicate(store, rip, block_id, ext_name, constraint):
    predicates = None
    constraint = preprocess_constraint(store, rip, block_id, ext_name, constraint)
    if constraint:
        logic_ops = re.findall(r'[<!=>]+', constraint)
        if len(logic_ops) > 1:
            operands = []
            rest = constraint
            for logic_op in logic_ops:
                lhs, rest = rest.split(logic_op, 1)
                operands.append(lhs.strip())
            operands.append(rest.strip())
            index = 0
            for logic_op in logic_ops:
                pred = parse_basic_pred(store, rip, block_id, logic_op, operands[index], operands[index+1])
                if pred is not None:
                    if predicates is not None:
                        predicates = simplify(And(predicates, pred))
                    else:
                        predicates = pred
                index += 1
        elif len(logic_ops) == 1:
            logic_op = logic_ops[0]
            lhs, rhs = constraint.split(logic_op)
            predicates = parse_basic_pred(store, rip, block_id, logic_op, lhs, rhs)
    return predicates


def parse_predicates(store, rip, block_id, ext_name, constraint):
    constraint_list = constraint.split('or')
    predicates = None
    for c in constraint_list:
        pred = parse_single_predicate(store, rip, block_id, ext_name, c)
        if pred is not None:
            if predicates is not None:
                predicates = simplify(Or(predicates, pred))
            else:
                predicates = pred
    return predicates


def insert_new_constraints(store, rip, block_id, ext_name, pre_constraint, constraint):
    new_constraint = constraint
    if pre_constraint:
        predicates = None
        for p_constraint in pre_constraint: 
            p_constraint = utils.remove_multiple_spaces(p_constraint)
            p_constraint = p_constraint.lower()
            pred = parse_predicates(store, rip, block_id, ext_name, p_constraint)
            if pred is not None:
                if predicates is not None:
                    predicates = simplify(And(predicates, pred))
                else:
                    predicates = pred
        if predicates is not None:
            new_constraint = Constraint(constraint, predicates)
    return new_constraint

