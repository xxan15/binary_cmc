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
from ..semantics import smt_helper
from ..semantics import semantics



def get_func_call_invariant_arguments(block_set, func_call_blk, src_names):
    indoubt_arguments = []
    invariant_arguments = []
    parent_blk = block_set[func_call_blk.parent_no]
    parent_store, curr_store = parent_blk.sym_store.store, func_call_blk.sym_store.store
    parent_rip, curr_rip = parent_blk.sym_store.rip, func_call_blk.sym_store.rip
    for src_name in src_names:
        if src_name in lib.REG_NAMES:
            prev_val = sym_engine.get_sym(parent_store, parent_rip, src_name)
            curr_val = sym_engine.get_sym(curr_store, curr_rip, src_name)
            if sym_helper.bvnum_eq(prev_val, curr_val):
                indoubt_arguments.append(src_name)
        else:
            invariant_arguments.append(src_name)
    return parent_blk, indoubt_arguments, invariant_arguments


# When a memory address is located in stack, we concretize the memory address
# by using the z3 SMT Solver to generate concrete value for symbolic values using the constraint
def resolve_value_for_stack_addr_inv_arg(mem_len_map, sym_store, stack_addr, substitute_pair, last_constraint):
    predicates = last_constraint.get_predicates()
    m = sym_helper.check_pred_satisfiable(predicates)
    if m is not False:
        stack_val_len = mem_len_map[stack_addr]
        stack_val = sym_engine.get_sym(sym_store.store, sym_store.rip, '[' + stack_addr + ']', stack_val_len)
        res = stack_val
        for d in m.decls():
            s_val = m[d]
            s_len = s_val.size()
            res = sym_helper.substitute_sym_val(res, sym_helper.bit_vec_wrap(d.name(), s_len), s_val)
            substitute_pair.append((sym_helper.bit_vec_wrap(d.name(), s_len), s_val))
        sym_engine.set_sym(sym_store.store, sym_store.rip, '[' + stack_addr + ']', res)


def pp_tb_debug_info(ret_type, address, inst):
    res = 'The path is unsound due to '
    res += ret_type.name.lower()
    res += ' at ' + hex(address) + ': ' + inst
    return res
    
