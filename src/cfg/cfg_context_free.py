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

from ..common import utils
from ..common import lib
from ..common.lib import TRACE_BACK_TYPE
from ..common.lib import TRACE_BACK_RET_TYPE
from .block import Block
from .constraint import Constraint
from .sym_store import Sym_Store
from . import trace_back
from . import cfg_helper
from . import properties
from ..semantics import semantics
from ..semantics import semantics_traceback
from ..semantics import smt_helper
from ..semantics import ext_handler
from ..symbolic import sym_helper
from ..symbolic import sym_engine


class CFG_Context_Free(object):
    def __init__(self, sym_table, address_sym_table, address_inst_map, address_next_map, start_address, main_address, func_name, func_call_order):
        self.block_set = {}
        self.block_stack = []
        self.address_block_map = {}
        self.loop_trace_counter = {}
        self.mem_len_map = {}
        self.sym_table = sym_table
        self.address_sym_table = address_sym_table
        self.start_address = start_address
        self.address_inst_map = address_inst_map
        self.address_next_map = address_next_map
        self.dummy_block = Block(None, None, '', None, None)
        self.main_address = main_address
        self.ret_call_address_map = {}
        self.address_jt_entries_map = {}
        self.invariant_argument_map = {}
        self.to_be_verified_func_store = {}
        self.last_sym_memaddr_tb_inst_address = None
        self.function_inedges_map = {}
        self.function_inedges_map['_start'] = {}
        self.function_inedges_map['main'] = {}
        self.function_inedges_map['main']['_start'] = []
        sym_store = Sym_Store(None, None, None)
        sym_store.store[lib.VERIFIED_FUNC_INFO] = (start_address, func_name)
        self.cmc_func_exec_info = {}
        self.cmc_func_exec_info[func_name] = [0] * utils.CMC_EXEC_RES_COUNT
        self.func_call_order = func_call_order
        constraint = None
        sym_helper.cnt_init()
        semantics.start_init(sym_store.store, start_address)
        cfg_helper.cfg_init_parameter(sym_store.store, self.sym_table)
        self.build_cfg(start_address, sym_store, constraint)
        self.cmc_exec_info = cfg_helper.collect_statistic_data_from_map(self.cmc_func_exec_info)
        
    
    def build_cfg(self, start_address, sym_store, constraint):
        start_inst = self.address_inst_map[start_address]
        self.add_new_block(None, start_address, start_inst, sym_store, constraint)
        while self.block_stack:
            curr = self.block_stack.pop()
            utils.logger.debug('%s: %s' % (hex(curr.address), curr.inst))
            # utils.logger.debug(curr.sym_store.pp_store())
            address, inst, sym_store, constraint = curr.address, curr.inst, curr.sym_store, curr.constraint
            if inst and inst.startswith('bnd '):
                inst = inst.strip().split(' ', 1)[1]
            if utils.check_branch_inst(inst):
                self.construct_branch(curr, address, inst, sym_store, constraint)
            else:
                new_address = cfg_helper.get_next_address(address, self.address_next_map, self.address_sym_table)
                if new_address != -1:
                    self.jump_to_block(curr, new_address, sym_store, constraint)
            if len(self.block_stack) == 0:
                self._add_next_to_be_verified_function(sym_store)
            

    def _add_next_to_be_verified_function(self, sym_store):
        _, verified_func_name = sym_store.store[lib.VERIFIED_FUNC_INFO]
        # Make a statistics on whether an invariant argument is modified 
        # during the execution of the current function
        for func_name in self.function_inedges_map[verified_func_name]:
            inv_args = self.function_inedges_map[verified_func_name][func_name]
            inv_args = list(set(inv_args))
            self.function_inedges_map[verified_func_name][func_name] = inv_args
            for idx, arg in enumerate(inv_args):
                if arg in sym_store.store[lib.TO_BE_VERIFIED_ARGS]:
                    tmp_res = sym_store.store[lib.TO_BE_VERIFIED_ARGS][arg][2]
                    inv_args[idx] = (arg, tmp_res)
                elif utils.imm_start_pat.match(arg):
                    arg = '[' + arg + ']'
                    tmp_res = sym_store.store[lib.TO_BE_VERIFIED_ARGS][arg][2]
                    # else:
                    #     tmp_res = None
                    inv_args[idx] = (arg, tmp_res)
                else:
                    inv_args[idx] = (arg, None)
        self._handle_termination_for_start(verified_func_name)
        utils.output_logger.info('The symbolic execution has been terminated for the function ' + verified_func_name + '\n')
        utils.logger.info('The symbolic execution has been terminated for the function ' + verified_func_name + '\n')
        curr_idx = self.func_call_order.index(verified_func_name)
        if curr_idx + 1 < len(self.func_call_order):
            next_func_name = self.func_call_order[curr_idx + 1]
            # print(next_func_name)
            # self.function_inedges_map[next_func_name] = {}
            # self.function_inedges_map[next_func_name][verified_func_name] = []
            self._release_unused_resources()
            if next_func_name not in self.to_be_verified_func_store and '@' not in next_func_name:
                self._create_new_symstore_w_to_be_verified_args(next_func_name)
            if '@' not in next_func_name:
                func_start_address, func_start_inst, new_sym_store = self.to_be_verified_func_store[next_func_name]
                ext_handler.insert_termination_symbol(new_sym_store.store, new_sym_store.rip)
                self.add_new_block(None, func_start_address, func_start_inst, new_sym_store, None)

    def _handle_termination_for_start(self, func_name):
        if func_name == '_start':
            # num of paths
            self.cmc_func_exec_info[func_name][0] += 1
            # sound cases
            self.cmc_func_exec_info[func_name][7] += 1

    def _release_unused_resources(self):
        self.block_set.clear()
        self.address_block_map.clear()


    def construct_conditional_branches(self, block, address, inst, new_address, sym_store, constraint):
        res = smt_helper.parse_predicate(sym_store.store, inst, True)
        if res == False:
            next_address = cfg_helper.get_next_address(address, self.address_next_map, self.address_sym_table)
            self.construct_conditional_jump_block(block, address, inst, next_address, sym_store, constraint, res)
        elif res == True:
            self.construct_conditional_jump_block(block, address, inst, new_address, sym_store, constraint, res)
        else:
            next_address = cfg_helper.get_next_address(address, self.address_next_map, self.address_sym_table)
            self.construct_conditional_jump_block(block, address, inst, next_address, sym_store, constraint, False)
            self.construct_conditional_jump_block(block, address, inst, new_address, sym_store, constraint, True)
            

    def construct_conditional_jump_block(self, block, address, inst, new_address, sym_store, constraint, val):
        if address in self.address_block_map:
            if (address, new_address) in self.loop_trace_counter:
                counter = self.loop_trace_counter[(address, new_address)]
                if counter < utils.MAX_LOOP_COUNT:
                    self.loop_trace_counter[(address, new_address)] += 1
                    self.jump_to_block_w_new_constraint(block, inst, new_address, sym_store, constraint, val)
            else:
                exists_loop = cfg_helper.detect_loop(block, address, new_address, self.block_set)
                if exists_loop:
                    self.loop_trace_counter[(address, new_address)] = 1
                self.jump_to_block_w_new_constraint(block, inst, new_address, sym_store, constraint, val)
        else:
            self.jump_to_block_w_new_constraint(block, inst, new_address, sym_store, constraint, val)
            

    def jump_to_block_w_new_constraint(self, block, inst, new_address, sym_store, constraint, val):
        new_constraint = self.add_new_constraint(sym_store.store, constraint, inst, val)
        # utils.logger.info(new_constraint)
        # res = self._check_path_reachability(new_constraint)
        # utils.logger.info(res)
        # if res:
        new_inst = self.address_inst_map[new_address]
        self.add_new_block(block, new_address, new_inst, sym_store, new_constraint)
        
        
    def construct_branch(self, block, address, inst, sym_store, constraint):
        if inst == 'ret' or inst.endswith(' ret'):
            self.build_ret_branch(block, address, inst, sym_store, constraint)
        else:
            jump_address_str = inst.split(' ', 1)[1].strip()
            new_address = smt_helper.get_jump_address(sym_store.store, sym_store.rip, jump_address_str)
            if new_address in self.address_inst_map and inst.startswith('call '):
                _, curr_func_name = sym_store.store[lib.VERIFIED_FUNC_INFO]
                new_func_name = cfg_helper.get_function_name_from_addr_sym_table(self.address_sym_table, new_address)
                if '@' not in new_func_name:
                    if new_func_name not in self.func_call_order:
                        self.func_call_order.append(new_func_name)
                    if new_func_name not in self.function_inedges_map:
                        self.function_inedges_map[new_func_name] = {}
                        self.function_inedges_map[new_func_name][curr_func_name] = []
                    elif curr_func_name not in self.function_inedges_map[new_func_name]:
                        self.function_inedges_map[new_func_name][curr_func_name] = []
                self.handle_external_function(new_func_name, block, address, inst, sym_store, constraint)
            elif new_address in self.address_inst_map:
                self.handle_internal_jumps(block, address, inst, sym_store, constraint, new_address)
            elif new_address in self.address_sym_table:
                ext_func_name = cfg_helper.get_function_name_from_addr_sym_table(self.address_sym_table, new_address)
                self.handle_external_function(ext_func_name, block, address, inst, sym_store, constraint)
            elif sym_helper.sym_is_int_or_bitvecnum(new_address):
                ext_func_name = 'undefined'
                self.handle_external_function(ext_func_name, block, address, inst, sym_store, constraint)
                utils.logger.debug('Jump to an undefined external address ' + str(new_address) + ' at address ' + hex(address))
            elif str(new_address).startswith(utils.MEM_DATA_SEC_SUFFIX):
                ext_func_name = str(new_address)
                self.handle_external_function(ext_func_name, block, address, inst, sym_store, constraint)
                utils.logger.debug('Jump to an undefined external address ' + str(new_address) + ' at address ' + hex(address))
            else:
                self.handle_unresolved_indirect_jumps(block, address, inst, constraint, new_address)
                

    def handle_internal_jumps(self, block, address, inst, sym_store, constraint, new_address):
        utils.logger.info(hex(address) + ': jump address is ' + sym_helper.string_of_address(new_address))
        if utils.check_not_single_branch_inst(inst):    # je xxx
            self.construct_conditional_branches(block, address, inst, new_address, sym_store, constraint)
        else:
            if new_address in self.address_block_map and new_address in self.address_sym_table and new_address in self.ret_call_address_map.values():
                if self._explored_func_block(sym_store, new_address):
                    func_name = cfg_helper.get_function_name_from_addr_sym_table(self.address_sym_table, new_address)
                    self.handle_external_function(func_name, block, address, inst, sym_store, constraint)
                else:
                    self.jump_to_block(block, new_address, sym_store, constraint)
            else:
                self.jump_to_block(block, new_address, sym_store, constraint)


    def handle_unresolved_indirect_jumps(self, block, address, inst, constraint, new_address):
        if inst.startswith('jmp ') and not inst.endswith(']'):
            trace_list = []
            if block.address in self.address_jt_entries_map:
                inst_dest, target_addresses = self.address_jt_entries_map[block.address]
                self._reconstruct_jump_targets(block, inst_dest, target_addresses)
                res = lib.TRACE_BACK_RET_TYPE.JT_SUCCEED
            else:
                res, _ = self.trace_back(block, [inst.split(' ', 1)[1].strip()], trace_list, TRACE_BACK_TYPE.INDIRECT)
            if res != lib.TRACE_BACK_RET_TYPE.JT_SUCCEED:
                if constraint is not None:
                    path_reachable = cfg_helper.check_path_reachability(constraint)
                    if path_reachable == False: return
                utils.logger.info('Cannot resolve the jump address ' + sym_helper.string_of_address(new_address) + ' of ' + inst + ' at address ' + hex(address))
                utils.logger.info(trace_back.pp_tb_debug_info(res, address, inst))
                # sys.exit('Cannot resolve the jump address ' + sym_helper.string_of_address(new_address) + ' of ' + inst + ' at address ' + hex(address))
        else:
            if constraint is not None:
                res = cfg_helper.check_path_reachability(constraint)
                if res == False: 
                    utils.logger.info('The path is infeasible at the jump address ' + sym_helper.string_of_address(new_address) + ' of ' + inst + ' at address ' + hex(address) + '\n')
                    return
            utils.logger.info('Cannot resolve the jump address ' + sym_helper.string_of_address(new_address) + ' of ' + inst + ' at address ' + hex(address))
            # sys.exit('Cannot resolve the jump address ' + sym_helper.string_of_address(new_address) + ' of ' + inst + ' at address ' + hex(address))


    def handle_external_function(self, ext_func_name, block, address, inst, sym_store, constraint):
        rip, store = sym_store.rip, sym_store.store
        if ext_func_name.startswith('pthread_create'):
            self._cfg_create_new_thread(ext_func_name, block, address, inst, sym_store, constraint)
        elif ext_func_name.startswith(('malloc', 'calloc', 'realloc')):
            ext_name = ext_func_name.split('@', 1)[0].strip()
            heap_addr = sym_store.store[lib.HEAP_ADDR]
            new_heap_addr = ext_handler.ext_alloc_mem_call(store, rip, heap_addr, ext_name)
            sym_store.store[lib.HEAP_ADDR] = new_heap_addr
            self.build_ret_branch(block, address, inst, sym_store, constraint)
        elif ext_func_name.startswith(('free')):
            ext_handler.ext_free_mem_call(store, rip)
            self.build_ret_branch(block, address, inst, sym_store, constraint)
        else:
            ext_handler.ext_func_call(store, rip)
            ext_name = ext_func_name.split('@', 1)[0].strip()
            if ext_name not in lib.TERMINATION_FUNCTIONS:
                self.build_ret_branch(block, address, inst, sym_store, constraint)
            else:
                utils.logger.info('The symbolic execution has been terminated at the path due to the call of the function ' + ext_name + '\n')


    def add_to_be_verified_functions(self):
        for func_name in self.invariant_argument_map:
            if func_name in self.to_be_verified_func_store:
                func_start_address, _, new_sym_store = self.to_be_verified_func_store[func_name]
                to_be_verified_args = self.invariant_argument_map[func_name]
                self._add_to_be_verified_arg_to_func_symstore(to_be_verified_args, new_sym_store, func_start_address)
            elif '@' not in func_name:
                self._create_new_symstore_w_to_be_verified_args(func_name)
        self.invariant_argument_map.clear()
                

    def build_ret_branch(self, block, address, inst, sym_store, constraint):
        new_address = semantics.ret(sym_store.store)
        if new_address != None:
            if sym_helper.sym_is_int_or_bitvecnum(new_address):
                utils.logger.info(hex(address) + ': the return address is {}'.format(hex(new_address)))
                if new_address in self.address_inst_map:
                    if new_address not in self.ret_call_address_map:
                        call_target = self._get_prev_inst_target(new_address)
                        if call_target:
                            self.ret_call_address_map[new_address] = call_target
                    self.jump_to_block(block, new_address, sym_store, constraint)
                else:
                    self.jump_to_dummy(block)
            elif sym_helper.is_term_address(new_address):
                self.jump_to_dummy(block)
                self.handle_cmc_path_termination(block, sym_store, new_address)
            else:
                if constraint is not None:
                    res = cfg_helper.check_path_reachability(constraint)
                    if res == False: return
                # utils.logger.info('Cannot resolve the return address of ' + inst + ' at address ' + hex(address))
                # sys.exit('Cannot resolve the return address of ' + inst + ' at address ' + hex(address))
            

    def handle_cmc_path_termination(self, block, sym_store, new_address):
        verified_func_start_addr, verified_func_name = sym_store.store[lib.VERIFIED_FUNC_INFO]
        # NUM_OF_PATHS
        self.cmc_func_exec_info[verified_func_name][0] += 1
        if sym_store.store[lib.POINTER_RELATED_ERROR]:
            # NUM_OF_NEGATIVES
            self.cmc_func_exec_info[verified_func_name][2] += 1
            self._update_pointer_related_error_info(sym_store.store, verified_func_name)
        else:
            # NUM_OF_POSITIVES
            self.cmc_func_exec_info[verified_func_name][1] += 1
            # Sound cases
            self.cmc_func_exec_info[verified_func_name][7] += 1
            properties.compare_arg_val_w_original(self.block_set, block, sym_store, verified_func_start_addr, new_address)
            properties.check_called_saved_regs_convention(sym_store, new_address)
            self.add_to_be_verified_functions()
            utils.output_logger.info('Function ' + verified_func_name + ' is verified at specific path.\n')
        utils.logger.info('The symbolic execution has been terminated at the path\n')
        

    def handle_unbounded_jump_table_w_tb(self, trace_list, src_names, boundary, blk):
        trace_list = trace_list[::-1]
        src_name = src_names[0]
        src_len = utils.get_sym_length(src_name)
        rip = blk.sym_store.rip
        src_sym = sym_engine.get_sym(blk.sym_store.store, rip, src_name, src_len)
        cjmp_blk_idx, jt_idx_upperbound = cfg_helper.gen_jt_idx_upperbound(trace_list, boundary)
        if not jt_idx_upperbound: return lib.TRACE_BACK_RET_TYPE.JT_NO_UPPERBOUND
        jt_assign_blk_idx, is_jt_assign_inst = cfg_helper.check_jump_table_assign_inst(trace_list, cjmp_blk_idx)
        if not is_jt_assign_inst: return lib.TRACE_BACK_RET_TYPE.JT_NOT_ASSIGN_INST
        jt_assign_blk = trace_list[jt_assign_blk_idx]
        distinct_entries, inst_dest, src_len = cfg_helper.get_distinct_jt_entries(jt_assign_blk, src_sym, jt_idx_upperbound, self.block_set)
        if not distinct_entries: return lib.TRACE_BACK_RET_TYPE.JT_NO_DISTINCT_ENTRIES
        sym_store_list = cfg_helper.reconstruct_jt_sym_stores(jt_assign_blk, distinct_entries, inst_dest, src_len)
        dest, target_addresses = cfg_helper.reconstruct_jt_target_addresses(trace_list, jt_assign_blk_idx, sym_store_list, self.address_jt_entries_map)
        if not target_addresses: return lib.TRACE_BACK_RET_TYPE.JT_NO_TARGET_ADDRESSES
        utils.logger.info(hex(trace_list[-1].address) + ': jump addresses resolved using jump table [' + ', '.join(map(lambda x: hex(sym_helper.int_from_sym(x)), target_addresses)) + ']')
        self._reconstruct_jump_targets(trace_list[-1], dest, target_addresses)
        return lib.TRACE_BACK_RET_TYPE.JT_SUCCEED


    # For all the blocks in the track-back list, if the instr in specific block is 
    # an internal function call, save the invariant-argument requirement for the function
    def retrieve_call_func_invariants(self, trace_list, src_names, verified_func_name):
        for blk in trace_list:
            if blk.inst.startswith('call '):
                _, indoubt_arguments, invariant_arguments = self.get_func_call_invariant_arguments(blk, src_names)
                if not invariant_arguments: return lib.TRACE_BACK_RET_TYPE.SYMADDR_NO_FUNC_INVARIANTS
                if indoubt_arguments: return lib.TRACE_BACK_RET_TYPE.SYMADDR_W_FUNC_INDOUBT
                func_name, _ = cfg_helper.retrieve_internal_call_inst_func_name(blk, self.address_inst_map, self.address_sym_table)
                if func_name:
                    if func_name not in self.invariant_argument_map:
                        self.invariant_argument_map[func_name] = invariant_arguments
                    else:
                        self.invariant_argument_map[func_name].extend(invariant_arguments)
                    if func_name not in self.function_inedges_map:
                        self.function_inedges_map[func_name] = {}
                    if func_name != verified_func_name:
                        self.function_inedges_map[func_name][verified_func_name] = invariant_arguments
                    if func_name not in self.func_call_order:
                        self.func_call_order.append(func_name)

    def handle_symbolized_mem_w_tb(self, trace_list, src_names, rest, verified_func_name):
        trace_list = trace_list[::-1]
        func_call_blk = trace_list[0]
        parent_blk, indoubt_arguments, invariant_arguments = self.get_func_call_invariant_arguments(func_call_blk, src_names)
        if not invariant_arguments: return lib.TRACE_BACK_RET_TYPE.SYMADDR_NO_FUNC_INVARIANTS
        if indoubt_arguments: return lib.TRACE_BACK_RET_TYPE.SYMADDR_W_FUNC_INDOUBT
        func_name, new_address = cfg_helper.retrieve_call_inst_func_name(func_call_blk, self.address_inst_map, self.address_sym_table)
        if func_name:
            if func_name not in self.invariant_argument_map:
                self.invariant_argument_map[func_name] = invariant_arguments
            else:
                self.invariant_argument_map[func_name].extend(invariant_arguments)
            if func_name != verified_func_name:
                self.function_inedges_map[func_name][verified_func_name] = invariant_arguments
        self._reconstruct_func_call_w_invariant_arguments(trace_list, parent_blk, invariant_arguments, func_name, new_address, rest)
        return lib.TRACE_BACK_RET_TYPE.SYMADDR_SUCCEED


    def get_func_call_invariant_arguments(self, func_call_blk, src_names):
        indoubt_arguments = []
        invariant_arguments = []
        parent_blk = self.block_set[func_call_blk.parent_no]
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


    def _reconstruct_func_call_w_invariant_arguments(self, trace_list, parent_blk, invariant_arguments, func_name, rip, rest):
        parent_store, parent_rip = parent_blk.sym_store.store, parent_blk.sym_store.rip    
        last_but_one_blk = trace_list[-2]
        last_but_one_sym_store = last_but_one_blk.sym_store
        last_blk = trace_list[-1]
        last_but_one_rip, last_but_one_store, last_constraint = last_but_one_sym_store.rip, last_but_one_sym_store.store, last_blk.constraint
        tmp_sym_store = Sym_Store(last_but_one_store, last_but_one_rip)
        sym_engine.reset_mem_content_pollute(tmp_sym_store.store)
        print_info, stack_addrs = cfg_helper.construct_print_info(parent_store, parent_rip, tmp_sym_store, rip, invariant_arguments)
        substitute_pair = []
        for inv_arg in invariant_arguments:
            if stack_addrs and inv_arg in stack_addrs:
                stack_addr = inv_arg
                if last_constraint:
                    self._resolve_value_for_stack_addr_inv_arg(tmp_sym_store, stack_addr, substitute_pair, last_constraint)
            else:
                length = lib.DEFAULT_REG_LEN
                if inv_arg not in lib.REG_NAMES:
                    length = self.mem_len_map[inv_arg]
                curr_val = cfg_helper.get_inv_arg_val(tmp_sym_store.store, tmp_sym_store.rip, inv_arg, length)
                prev_val = cfg_helper.get_inv_arg_val(parent_store, parent_rip, inv_arg, curr_val.size())
                substitute_pair.append((curr_val, prev_val))
                cfg_helper.substitute_inv_arg_val_direct(tmp_sym_store.store, tmp_sym_store.rip, inv_arg, prev_val)
        for sym_arg, sym_new in substitute_pair:
            cfg_helper.substitute_sym_arg_for_all(tmp_sym_store.store, sym_arg, sym_new)
        if print_info:
            utils.output_logger.info('Assumption: the value at ' + print_info + ' not modified after the call of function ' + func_name)
        self.add_new_block(last_but_one_blk, last_blk.address, last_blk.inst, tmp_sym_store, last_blk.constraint)


    def trace_back(self, blk, sym_names, trace_list, tb_type):
        utils.logger.info('trace back')
        for _ in range(utils.MAX_TRACEBACK_COUNT):
            if blk.parent_no in self.block_set:
                p_store = self.block_set[blk.parent_no].sym_store.store
            else:
                if blk.inst.startswith('cmp'):
                    p_store = blk.sym_store.store
                else:
                    return lib.TRACE_BACK_RET_TYPE.TB_PARENT_BLOCK_DOES_NOT_EXIST, sym_names
            # p_store = self.block_set[blk.parent_no].sym_store.store
            src_names, need_stop, boundary, still_tb, func_call_point, rest, mem_len_map = semantics_traceback.parse_sym_src(self.address_sym_table, self.address_inst_map, p_store, blk.sym_store.rip, blk.inst, sym_names, tb_type)
            self.mem_len_map.update(mem_len_map)
            utils.logger.info(hex(blk.address) + ': ' + blk.inst)
            utils.logger.info(src_names)
            if func_call_point:
                trace_list.append(blk)
                # Prevent repeated tracing back: have already handled symbolic memory address problem 
                # at this instruction address in the trace-back model. 
                # However, the problem has not been solved
                # if self.last_sym_memaddr_tb_inst_address:
                #     if self.last_sym_memaddr_tb_inst_address == blk.address:
                #         return -2, src_names
                #     else:
                #         self.last_sym_memaddr_tb_inst_address = blk.address
                # else:
                #     self.last_sym_memaddr_tb_inst_address = blk.address
                _, verified_func_name = blk.sym_store.store[lib.VERIFIED_FUNC_INFO]
                self.retrieve_call_func_invariants(trace_list, src_names, verified_func_name)
                res = self.handle_symbolized_mem_w_tb(trace_list, src_names, rest, verified_func_name)
                return res, src_names
            elif need_stop and len(src_names) == 1:
                res = self.handle_unbounded_jump_table_w_tb(trace_list, src_names, boundary, blk)
                return res, src_names
            elif still_tb:
                trace_list.append(blk)
                blk = self.block_set[blk.parent_no]
                sym_names = src_names
            else: 
                utils.logger.info('\n')
                break
        return lib.TRACE_BACK_RET_TYPE.UNRESOLVED, sym_names


    def jump_to_block(self, block, new_address, sym_store, constraint):
        new_inst = self.address_inst_map[new_address]
        self.add_new_block(block, new_address, new_inst, sym_store, constraint)
            

    def jump_to_dummy(self, block):
        block.add_to_children_list(self.dummy_block.block_no)
        

    def add_new_block(self, parent_blk, address, inst, sym_store, constraint):
        rip = cfg_helper.get_next_address(address, self.address_next_map, self.address_sym_table)
        if inst.startswith('bnd '):
            inst = inst.strip().split(' ', 1)[1]
        if inst.startswith('cmov'):
            self._add_new_block_w_cmov_inst(parent_blk, address, inst, sym_store, constraint, rip)
        else:
            sym_store = Sym_Store(sym_store.store, rip, inst)
            self._add_new_block(parent_blk, address, inst, sym_store, constraint)


    def _add_new_block(self, parent_blk, address, inst, sym_store, constraint):
        if inst.startswith('bnd '):
            inst = inst.strip().split(' ', 1)[1]
        if sym_store.store[lib.NEED_TRACE_BACK]:
            self._handle_symbolized_mem_addr_w_traceback(parent_blk, address, inst, sym_store, constraint)
        elif sym_store.store[lib.POINTER_RELATED_ERROR]:
            self._terminate_path_w_pointer_related_errors(sym_store, address, inst)
        else:
            parent_no = parent_blk.block_no if parent_blk is not None else None
            block = Block(parent_no, address, inst.strip(), sym_store, constraint)
            block_no = block.block_no
            self.block_set[block_no] = block
            if parent_blk:
                parent_blk.add_to_children_list(block_no)
            if address in self.address_block_map:
                self.address_block_map[address].append(block)
            else:
                self.address_block_map[address] = [block]
            self.block_stack.append(block)


    def add_new_constraint(self, store, constraint, inst, val, prefix='j'):
        new_constraint = constraint
        pred_expr = smt_helper.parse_predicate(store, inst, val, prefix)
        if pred_expr != None:
            new_constraint = Constraint(constraint, pred_expr)
        return new_constraint


    def _handle_symbolized_mem_addr_w_traceback(self, parent_blk, address, inst, sym_store, constraint):
        trace_list = []
        inst_split = inst.strip().split(' ', 1)
        inst_args = utils.parse_inst_args(inst_split)
        utils.logger.info(inst_args[0])
        self.mem_len_map = {}
        new_srcs, _ = smt_helper.get_bottom_source(inst_args[0], sym_store.store, sym_store.rip, self.mem_len_map)
        res, sym_names = self.trace_back(parent_blk, new_srcs, trace_list, TRACE_BACK_TYPE.SYMBOLIC)
        if res != lib.TRACE_BACK_RET_TYPE.SYMADDR_SUCCEED:
            if constraint is not None:
                path_reachable = cfg_helper.check_path_reachability(constraint)
                if path_reachable == False: return
            # tmp = hex(address) + ': ' + inst
            if 'rdi' in sym_names:
                utils.output_logger.info('The path is unsound due to the unresolved value of argc\n')
            utils.logger.info(trace_back.pp_tb_debug_info(res, address, inst))
            utils.output_logger.info(trace_back.pp_tb_debug_info(res, address, inst))
            # Unresolved symbolic memory address
            _, curr_func_name = sym_store.store[lib.VERIFIED_FUNC_INFO]
            self.cmc_func_exec_info[curr_func_name][6] += 1
        

    def _terminate_path_w_pointer_related_errors(self, sym_store, address, inst):
        _, func_name = sym_store.store[lib.VERIFIED_FUNC_INFO]
        utils.output_logger.info('Pointer-related error at ' + hex(address) + ': ' + inst + '\n')
        # NUM_OF_PATHS
        self.cmc_func_exec_info[func_name][0] += 1
        # NUM_OF_NEGATIVES
        self.cmc_func_exec_info[func_name][2] += 1
        self._update_pointer_related_error_info(sym_store.store, func_name)
        

    def _create_new_symstore_w_to_be_verified_args(self, func_name):
        new_sym_store = Sym_Store(None, None, None)
        func_start_address = self.sym_table[func_name]
        func_start_inst = self.address_inst_map[func_start_address]
        semantics.start_init(new_sym_store.store, func_start_address)
        cfg_helper.cfg_init_parameter(new_sym_store.store, self.sym_table)
        new_sym_store.store[lib.VERIFIED_FUNC_INFO] = (func_start_address, func_name)
        self.cmc_func_exec_info[func_name] = [0] * utils.CMC_EXEC_RES_COUNT
        sym_x = sym_helper.gen_sym_x()
        smt_helper.push_val(new_sym_store.store, func_start_address, sym_x)
        to_be_verified_args = self.invariant_argument_map.get(func_name, [])
        self._add_to_be_verified_arg_to_func_symstore(to_be_verified_args, new_sym_store, func_start_address)
        self._preserve_callee_saved_regs_value(new_sym_store, func_start_address)
        self.to_be_verified_func_store[func_name] = (func_start_address, func_start_inst, new_sym_store)
        # sym_store = Sym_Store(new_sym_store.store, func_start_address, func_start_inst)
        # self._add_new_block(None, func_start_address, func_start_inst, sym_store, new_constraint)


    def _add_new_block_w_cmov_inst(self, parent_blk, address, inst, sym_store, constraint, rip):
        prefix = 'cmov'
        res = smt_helper.parse_predicate(sym_store.store, inst, True, prefix)
        if res == True:
            self._add_block_based_on_predicate(parent_blk, address, inst, sym_store, constraint, rip, True)
        elif res == False:
            self._add_block_based_on_predicate(parent_blk, address, inst, sym_store, constraint, rip, False)
        else:
            self._add_block_based_on_predicate(parent_blk, address, inst, sym_store, constraint, rip, True)
            self._add_block_based_on_predicate(parent_blk, address, inst, sym_store, constraint, rip, False)


    def _update_pointer_related_error_info(self, store, func_name):
        if store[lib.POINTER_RELATED_ERROR] == lib.MEMORY_RELATED_ERROR_TYPE.NULL_POINTER_DEREFERENCE:
            self.cmc_func_exec_info[func_name][3] += 1
        elif store[lib.POINTER_RELATED_ERROR] == lib.MEMORY_RELATED_ERROR_TYPE.USE_AFTER_FREE:
            self.cmc_func_exec_info[func_name][4] += 1
        elif store[lib.POINTER_RELATED_ERROR] == lib.MEMORY_RELATED_ERROR_TYPE.BUFFER_OVERFLOW:
            self.cmc_func_exec_info[func_name][5] += 1


    def _add_block_based_on_predicate(self, parent_blk, address, inst, sym_store, constraint, rip, pred):
        sym_store = Sym_Store(sym_store.store, rip)
        semantics.cmov(sym_store.store, rip, inst, pred)
        self._add_new_block(parent_blk, address, inst, sym_store, constraint)


    def _reconstruct_jump_targets(self, blk, inst_dest, target_addresses):
        address, inst = blk.address, blk.inst
        rip, store, constraint = blk.sym_store.rip, blk.sym_store.store, blk.constraint
        for target_addr in target_addresses:
            new_sym_store = Sym_Store(store, rip)
            sym_engine.set_sym(new_sym_store.store, rip, inst_dest, target_addr)
            self._add_new_block(blk, address, inst, new_sym_store, constraint)


    def _get_prev_inst_target(self, address):
        target = None
        p_address = cfg_helper.get_prev_address(address, self.address_inst_map)
        if p_address:
            p_inst = self.address_inst_map[p_address]
            if p_inst.startswith('call'):
                blk = self.address_block_map[p_address][0]
                jmp_target = smt_helper.get_jump_address(blk.sym_store.store, address, p_inst.split(' ', 1)[1].strip())
                if sym_helper.sym_is_int_or_bitvecnum(jmp_target):
                    target = jmp_target
        return target


    def _resolve_value_for_stack_addr_inv_arg(self, sym_store, stack_addr, substitute_pair, last_constraint):
        predicates = last_constraint.get_predicates()
        m = sym_helper.check_pred_satisfiable(predicates)
        if m is not False:
            stack_val_len = self.mem_len_map[stack_addr]
            stack_val = sym_engine.get_sym(sym_store.store, sym_store.rip, '[' + stack_addr + ']', stack_val_len)
            res = stack_val
            for d in m.decls():
                s_val = m[d]
                s_len = s_val.size()
                res = sym_helper.substitute_sym_val(res, sym_helper.bit_vec_wrap(d.name(), s_len), s_val)
                substitute_pair.append((sym_helper.bit_vec_wrap(d.name(), s_len), s_val))
            sym_engine.set_sym(sym_store.store, sym_store.rip, '[' + stack_addr + ']', res)



    def _explored_func_block(self, sym_store, new_address):
        blk_list = self.address_block_map[new_address]
        cnt = len(blk_list)
        if cnt > utils.MAX_VISIT_COUNT: return True
        elif cnt == 0: return False
        blk = blk_list[-1]
        prev_sym_store = blk.sym_store
        new_inst = self.address_inst_map[new_address]
        new_sym_store = Sym_Store(sym_store.store, prev_sym_store.rip, new_inst)
        res = new_sym_store.state_ith_eq(prev_sym_store) and new_sym_store.aux_mem_eq(prev_sym_store, lib.AUX_MEM)
        return res


    def _cfg_create_new_thread(self, ext_func_name, block, address, inst, sym_store, constraint):  
        store, rip = sym_store.store, sym_store.rip
        jmp_sym_store = Sym_Store(store, rip)
        sym_rdi = sym_engine.get_sym(store, rip, 'rdi')
        if sym_helper.sym_is_int_or_bitvecnum(sym_rdi):
            semantics.ret(jmp_sym_store.store)
            rdi_val = sym_helper.int_from_sym(sym_rdi)
            if rdi_val in self.address_inst_map:
                utils.logger.info(hex(address) + ': jump address is ' + sym_helper.string_of_address(rdi_val))
                self.jump_to_block(block, rdi_val, jmp_sym_store, constraint)
        fall_through_sym_store = Sym_Store(store, rip)
        ext_handler.ext_func_call(fall_through_sym_store.store, fall_through_sym_store.rip)
        self.build_ret_branch(block, address, inst, fall_through_sym_store, constraint)  


    def _preserve_callee_saved_regs_value(self, sym_store, rip):
        to_be_preserved_regs = lib.CALLEE_SAVED_REGS
        for reg in to_be_preserved_regs:
            prev_val = sym_engine.get_sym(sym_store.store, rip, reg)
            sym_store.store[lib.CALLEE_SAVED_REG_INFO][reg] = prev_val
        

    def _add_to_be_verified_arg_to_func_symstore(self, to_be_verified_args, new_sym_store, func_start_address):
        for arg in to_be_verified_args:
            length = lib.DEFAULT_REG_LEN
            if arg not in lib.REG_NAMES:
                length = self.mem_len_map[arg]
            if utils.imm_start_pat.match(arg):
                arg = '[' + arg + ']'
                self.mem_len_map[arg] = length
            prev_val = sym_engine.get_sym(new_sym_store.store, func_start_address, arg, length)
            tmp_res = None
            new_sym_store.store[lib.TO_BE_VERIFIED_ARGS][arg] = [prev_val, length, tmp_res]


    def draw_callgraph(self, file_path):
        res = 'digraph callgraph {\n'
        res += '    node [shape=record];\n'
        for name in self.func_call_order:
            res += self.draw_block(name)
        res += '\n'
        res += self.draw_demonstration()
        for name, in_edge_map in self.function_inedges_map.items():
            res += self.draw_edges(name, in_edge_map)
        res += '}'
        with open(file_path + '.dot', 'w+') as f:
            f.write(res)
        utils.convert_dot_to_png(file_path)


    def draw_block(self, name):
        res = '    ' + utils.replace_dot_in_func_name(name) 
        res += ' [label=<<table border="0" cellspacing="0">'
        res += '<tr><td colspan="5">' + name + '</td></tr>'
        res += self.pp_pointer_related_error_info(name)
        res += '</table>>];\n'
        return res


    def pp_color_demonstr(self, color, statement):
        res = '<tr>'
        res += '<td border="0" bgcolor="' + color + '"></td>'
        res += '<td colspan="4">' + statement + '</td>'
        res += '</tr>'
        return res


    def draw_demonstration(self):
        res = '    color_demonstration' 
        res += ' [label=<<table border="0" cellspacing="0">'
        for color, statement in lib.COLOR_ERROR_MAPPING.items():
            res += self.pp_color_demonstr(color, statement)
        res += '</table>>];\n'
        return res


    def pp_pointer_related_error_info(self, name):
        res = ''
        if name in self.cmc_func_exec_info:
            res += '<tr>'
            func_exec_info = self.cmc_func_exec_info[name]
            # Null pointer dereference error
            res += self._pp_specific_error_info(func_exec_info, 3, 'red')
            # Use after free error
            res += self._pp_specific_error_info(func_exec_info, 4, 'purple')
            # Buffer overflow
            res += self._pp_specific_error_info(func_exec_info, 5, 'grey')
            # Unresolved symbolic memory address
            res += self._pp_specific_error_info(func_exec_info, 6, 'yellow')
            # Sound
            res += self._pp_specific_error_info(func_exec_info, 7, 'green')
            res += '</tr>'
        return res


    def _pp_specific_error_info(self, func_exec_info, index, color):
        res = ''
        res += '<td port="port' + str(index) + '" border="0" bgcolor="' + color + '">' + str(func_exec_info[index]) + '</td>'
        return res


    def draw_edges(self, name, in_edge_map):
        res = ''
        for in_name, in_labels in in_edge_map.items():
            res += '    ' + utils.replace_dot_in_func_name(in_name)
            res += ' -> '
            res += utils.replace_dot_in_func_name(name)
            if in_labels:
                res += ' [label=<<table border="0" cellspacing="0" cellborder="1">'
                res += '\n'.join(map(lambda i: self.pp_edge_label(i), in_labels))
                res += '</table>>]'
            res += ';\n'
        return res


    def pp_edge_label(self, edge_label):
        res = '<tr>\n<td>'
        if len(edge_label) == 2:
            arg, pred = edge_label
            if pred is not None:
                if pred:
                    res += str(arg)
                else:
                    res += '<u>' + str(arg) + '</u>'
            else:
                res += str(arg)
        else:
            res += str(edge_label)
        res += '</td>\n</tr>'
        return res

    def reachable_addresses_num(self):
        res = len(list(self.address_block_map.keys()))
        return res
            
