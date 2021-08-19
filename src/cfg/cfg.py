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
from .block import Block
from .constraint import Constraint
from .sym_store import Sym_Store
from . import cfg_helper
from ..semantics import semantics
from ..semantics import semantics_traceback
from ..semantics import smt_helper
from ..semantics import ext_handler
from ..symbolic import sym_helper
from ..symbolic import sym_engine


class CFG(object):
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
        # self.to_be_visited_func = {'main'}
        self.last_sym_memaddr_tb_inst_address = None
        sym_store = Sym_Store(None, None, None)
        sym_store.store[lib.VERIFIED_FUNC_INFO] = (start_address, func_name)
        self.cmc_func_exec_info = {}
        self.cmc_func_exec_info[func_name] = [0, 0, 0]
        self.func_call_order = func_call_order
        constraint = None
        sym_helper.cnt_init()
        semantics.start_init(sym_store.store, start_address)
        cfg_helper.cfg_init_parameter(sym_store.store, self.sym_table)
        self.build_cfg(start_address, sym_store, constraint)

    
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
                _, verified_func_name = sym_store.store[lib.VERIFIED_FUNC_INFO]
                utils.output_logger.info('The symbolic execution has been terminated for the function ' + verified_func_name + '\n')
                utils.logger.info('The symbolic execution has been terminated for the function ' + verified_func_name + '\n')
                curr_idx = self.func_call_order.index(verified_func_name)
                # to_visit = False
                # while curr_idx + 1 < len(self.func_call_order):
                #     next_func_name = self.func_call_order[curr_idx + 1]
                #     if next_func_name in self.to_be_visited_func:
                #         to_visit = True
                #         break
                #     curr_idx += 1
                # if to_visit:
                if curr_idx + 1 < len(self.func_call_order):
                    next_func_name = self.func_call_order[curr_idx + 1]
                    print(next_func_name)
                    # for func_name in self.to_be_verified_func_store:
                    if next_func_name not in self.to_be_verified_func_store:
                        self._create_new_symstore_w_to_be_verified_args(next_func_name)
                    func_start_address, func_start_inst, new_sym_store = self.to_be_verified_func_store[next_func_name]
                    self.add_new_block(None, func_start_address, func_start_inst, new_sym_store, None)

        

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
                func_name = self.address_sym_table[new_address][0]
                if func_name not in self.func_call_order:
                    self.func_call_order.append(func_name)
                # self.to_be_visited_func.add(func_name)
                self.external_branch(func_name, block, address, inst, sym_store, constraint)
            elif new_address in self.address_inst_map:
                utils.logger.info(hex(address) + ': jump address is ' + sym_helper.string_of_address(new_address))
                if utils.check_not_single_branch_inst(inst):    # je xxx
                    self.construct_conditional_branches(block, address, inst, new_address, sym_store, constraint)
                else:
                    if new_address in self.address_block_map and new_address in self.address_sym_table and new_address in self.ret_call_address_map.values():
                        if self._explored_func_block(sym_store, new_address):
                            func_name = self.address_sym_table[new_address][0]
                            self.external_branch(func_name, block, address, inst, sym_store, constraint)
                        else:
                            self.jump_to_block(block, new_address, sym_store, constraint)
                    else:
                        self.jump_to_block(block, new_address, sym_store, constraint)
            elif new_address in self.address_sym_table:
                ext_func_name = self.address_sym_table[new_address][0]
                self.external_branch(ext_func_name, block, address, inst, sym_store, constraint)
            elif sym_helper.sym_is_int_or_bitvecnum(new_address):
                ext_func_name = 'undefined'
                self.external_branch(ext_func_name, block, address, inst, sym_store, constraint)
                utils.logger.debug('Jump to an undefined external address ' + str(new_address) + ' at address ' + hex(address))
            elif str(new_address).startswith(utils.MEM_DATA_SEC_SUFFIX):
                ext_func_name = str(new_address)
                self.external_branch(ext_func_name, block, address, inst, sym_store, constraint)
                utils.logger.debug('Jump to an undefined external address ' + str(new_address) + ' at address ' + hex(address))
            else:
                self.handle_unresolved_indirect_jumps(block, address, inst, constraint, new_address)
                

    def handle_unresolved_indirect_jumps(self, block, address, inst, constraint, new_address):
        if inst.startswith('jmp ') and not inst.endswith(']'):
            trace_list = []
            if block.address in self.address_jt_entries_map:
                inst_dest, target_addresses = self.address_jt_entries_map[block.address]
                self._reconstruct_jump_targets(block, inst_dest, target_addresses)
                res = 0
            else:
                res, _ = self.trace_back(block, [inst.split(' ', 1)[1].strip()], trace_list, TRACE_BACK_TYPE.INDIRECT)
            if res == -1:
                if constraint is not None:
                    res = cfg_helper.check_path_reachability(constraint)
                    if res == False:
                        return
                utils.logger.info('Cannot resolve the jump address ' + sym_helper.string_of_address(new_address) + ' of ' + inst + ' at address ' + hex(address))
                # sys.exit('Cannot resolve the jump address ' + sym_helper.string_of_address(new_address) + ' of ' + inst + ' at address ' + hex(address))
        else:
            if constraint is not None:
                res = cfg_helper.check_path_reachability(constraint)
                if res == False: 
                    utils.logger.info('The path is infeasible at the jump address ' + sym_helper.string_of_address(new_address) + ' of ' + inst + ' at address ' + hex(address) + '\n')
                    return
            utils.logger.info('Cannot resolve the jump address ' + sym_helper.string_of_address(new_address) + ' of ' + inst + ' at address ' + hex(address))
            # sys.exit('Cannot resolve the jump address ' + sym_helper.string_of_address(new_address) + ' of ' + inst + ' at address ' + hex(address))
                

    def external_branch(self, ext_func_name, block, address, inst, sym_store, constraint):
        # utils.logger.debug('Execute the function: ' + ext_func_name + '\n')
        rip, store = sym_store.rip, sym_store.store
        # if ext_func_name.startswith('__libc_start_main'):
        #     semantics.call(store, rip)
        #     next_address = self.main_address
        #     utils.logger.info(hex(address) + ': jump address is ' + sym_helper.string_of_address(next_address))
        #     ext_handler.ext__libc_start_main(store, rip, self.main_address)
        #     self.preserve_callee_saved_regs_value(sym_store, next_address)
        #     self.jump_to_block(block, next_address, sym_store, constraint)
        # el
        if ext_func_name == 'pthread_create':
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
            ext_handler.ext_func_call(fall_through_sym_store.store, fall_through_sym_store.rip, ext_func_name)
            self.build_ret_branch(block, address, inst, fall_through_sym_store, constraint)
        elif ext_func_name in (('malloc', 'calloc', 'realloc')):
            heap_addr = sym_store.store[lib.HEAP_ADDR]
            new_heap_addr = ext_handler.ext_alloc_mem_call(store, rip, heap_addr, ext_func_name)
            sym_store.store[lib.HEAP_ADDR] = new_heap_addr
            self.build_ret_branch(block, address, inst, sym_store, constraint)
        elif ext_func_name in (('free')):
            _ = ext_handler.ext_free_mem_call(store, rip)
            self.build_ret_branch(block, address, inst, sym_store, constraint)
        else:
            ext_handler.ext_func_call(store, rip, ext_func_name)
            ext_name = ext_func_name.split('@', 1)[0].strip()
            if ext_name not in lib.TERMINATION_FUNCTIONS:
                self.build_ret_branch(block, address, inst, sym_store, constraint)
            else:
                utils.logger.info('The symbolic execution has been terminated at the path due to the call of the function ' + ext_name + '\n')


    def preserve_callee_saved_regs_value(self, sym_store, rip):
        to_be_preserved_regs = lib.CALLEE_SAVED_REGS
        for reg in to_be_preserved_regs:
            prev_val = sym_engine.get_sym(sym_store.store, rip, reg)
            sym_store.store[lib.CALLEE_SAVED_REG_INFO][reg] = prev_val
        

    def _create_new_symstore_w_to_be_verified_args(self, func_name):
        new_sym_store = Sym_Store(None, None, None)
        func_start_address = self.sym_table[func_name]
        func_start_inst = self.address_inst_map[func_start_address]
        semantics.start_init(new_sym_store.store, func_start_address)
        cfg_helper.cfg_init_parameter(new_sym_store.store, self.sym_table)
        new_sym_store.store[lib.VERIFIED_FUNC_INFO] = (func_start_address, func_name)
        self.cmc_func_exec_info[func_name] = [0, 0, 0]
        sym_x = sym_helper.gen_sym_x()
        smt_helper.push_val(new_sym_store.store, func_start_address, sym_x)
        to_be_verified_args = self.invariant_argument_map.get(func_name, [])
        self._add_to_be_verified_arg_to_func_symstore(to_be_verified_args, new_sym_store, func_start_address)
        self.preserve_callee_saved_regs_value(new_sym_store, func_start_address)
        self.to_be_verified_func_store[func_name] = (func_start_address, func_start_inst, new_sym_store)
        # sym_store = Sym_Store(new_sym_store.store, func_start_address, func_start_inst)
        # self._add_new_block(None, func_start_address, func_start_inst, sym_store, new_constraint)


    def _add_to_be_verified_arg_to_func_symstore(self, to_be_verified_args, new_sym_store, func_start_address):
        for arg in to_be_verified_args:
            length = lib.DEFAULT_REG_LEN
            if arg not in lib.REG_NAMES:
                length = self.mem_len_map[arg]
            if utils.imm_start_pat.match(arg):
                arg = '[' + arg + ']'
                self.mem_len_map[arg] = length
            prev_val = sym_engine.get_sym(new_sym_store.store, func_start_address, arg, length)
            new_sym_store.store[lib.TO_BE_VERIFIED_ARGS][arg] = prev_val


    def add_to_be_verified_functions(self):
        for func_name in self.invariant_argument_map:
            if func_name in self.to_be_verified_func_store:
                func_start_address, _, new_sym_store = self.to_be_verified_func_store[func_name]
                to_be_verified_args = self.invariant_argument_map[func_name]
                self._add_to_be_verified_arg_to_func_symstore(to_be_verified_args, new_sym_store, func_start_address)
            else:
                self._create_new_symstore_w_to_be_verified_args(func_name)
        self.invariant_argument_map.clear()
                

    def _check_changed_arg_val_position(self, block, sym_store, start_address, arg, length):
        func_list = []
        blk = block
        store = sym_store.store
        parent_no = block.parent_no
        while parent_no:
            parent_blk = self.block_set[parent_no]
            parent_store = parent_blk.sym_store.store
            if parent_blk.address != start_address:
                if blk.inst.startswith('call '):
                    parent_val = sym_engine.get_sym(parent_store, blk.address, arg, length)
                    curr_val = sym_engine.get_sym(store, blk.sym_store.rip, arg, length)
                    if not sym_helper.bitvec_eq(parent_val, curr_val):
                        func_name, _ = cfg_helper.retrieve_internal_call_inst_func_name(blk, self.address_inst_map, self.address_sym_table)
                        func_list.append(func_name)
            else:
                if blk.inst.startswith('call '):
                    parent_val = sym_engine.get_sym(parent_store, blk.address, arg, length)
                    curr_val = sym_engine.get_sym(store, blk.sym_store.rip, arg, length)
                    if not sym_helper.bitvec_eq(parent_val, curr_val):
                        func_name, _ = cfg_helper.retrieve_internal_call_inst_func_name(blk, self.address_inst_map, self.address_sym_table)
                        func_list.append(func_name)
                break
            parent_no = parent_blk.parent_no
            blk = parent_blk
            store = parent_store
        return func_list


    def check_called_saved_regs_convention(self, sym_store, new_address):
        if len(sym_store.store[lib.CALLEE_SAVED_REG_INFO]) > 0:
            res = True
            for reg in sym_store.store[lib.CALLEE_SAVED_REG_INFO]:
                prev_val = sym_store.store[lib.CALLEE_SAVED_REG_INFO][reg]
                new_val = sym_engine.get_sym(sym_store.store, new_address, reg)
                if not sym_helper.strict_bitvec_equal(prev_val, new_val):
                    res = False
                    utils.output_logger.info('Function ' + sym_store.store[lib.VERIFIED_FUNC_INFO][1] + ' does NOT save the value at register ' + reg + ' at specific path.\n')
            args = list(sym_store.store[lib.CALLEE_SAVED_REG_INFO].keys())
            if res:
                utils.output_logger.info('Function ' + sym_store.store[lib.VERIFIED_FUNC_INFO][1] + ' DOES save the value at registers ' + str(args) + ' at specific path.\n')


    def compare_arg_val_w_original(self, block, sym_store, start_address, new_address):
        if len(sym_store.store[lib.TO_BE_VERIFIED_ARGS]) > 0:
            res = True
            for arg in sym_store.store[lib.TO_BE_VERIFIED_ARGS]:
                length = lib.DEFAULT_REG_LEN
                if arg not in lib.REG_NAMES:
                    length = self.mem_len_map[arg]
                prev_val = sym_store.store[lib.TO_BE_VERIFIED_ARGS][arg]
                new_val = sym_engine.get_sym(sym_store.store, new_address, arg, length)
                if not sym_helper.strict_bitvec_equal(prev_val, new_val):
                    if sym_helper.is_bv_sym_var(new_val):
                        res = False
                        func_list = self._check_changed_arg_val_position(block, sym_store, start_address, arg, length)
                        if func_list:
                            utils.output_logger.info('Function ' + sym_store.store[lib.VERIFIED_FUNC_INFO][1] + ' might preserve the value at ' + arg + ' if ' + str(func_list) + ' preserve ' + arg + ' at specific path.\n')
                        else:
                            utils.output_logger.info('Function ' + sym_store.store[lib.VERIFIED_FUNC_INFO][1] + ' does NOT preserve the value at ' + arg + ' at specific path.\n')
                    else:
                        res = False
                        utils.output_logger.info('Function ' + sym_store.store[lib.VERIFIED_FUNC_INFO][1] + ' does NOT preserve the value at ' + arg + ' at specific path.\n')
            args = list(sym_store.store[lib.TO_BE_VERIFIED_ARGS].keys())
            if res:
                utils.output_logger.info('Function ' + sym_store.store[lib.VERIFIED_FUNC_INFO][1] + ' DOES preserve the value at ' + str(args) + ' at specific path.\n')


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
                self.handle_cmc_path_termination(block, sym_store, constraint, new_address)
            else:
                if constraint is not None:
                    res = cfg_helper.check_path_reachability(constraint)
                    if res == False: return
                # utils.logger.info('Cannot resolve the return address of ' + inst + ' at address ' + hex(address))
                # sys.exit('Cannot resolve the return address of ' + inst + ' at address ' + hex(address))
            

    def handle_cmc_path_termination(self, block, sym_store, constraint, new_address):
        verified_func_start_addr, verified_func_name = sym_store.store[lib.VERIFIED_FUNC_INFO]
        # NUM_OF_PATHS
        self.cmc_func_exec_info[verified_func_name][0] += 1
        if not sym_store.store[lib.POINTER_RELATED_ERROR]:
            # NUM_OF_POSITIVES
            self.cmc_func_exec_info[verified_func_name][1] += 1
            if constraint is not None:
                res = cfg_helper.check_unsatisfied_input(constraint)
                if res == False:
                    self.compare_arg_val_w_original(block, sym_store, verified_func_start_addr, new_address)
                    self.check_called_saved_regs_convention(sym_store, new_address)
                    self.add_to_be_verified_functions()
                    utils.output_logger.info('Function ' + verified_func_name + ' is verified at specific path under above-mentioned assumptions.\n')
                else:
                    p_info = sym_helper.pp_z3_model_info(res)
                    utils.output_logger.info('Function ' + verified_func_name + ' is unsound at specific path with following arguments: ' + p_info + '\n')
            else:
                self.compare_arg_val_w_original(block, sym_store, verified_func_start_addr, new_address)
                self.check_called_saved_regs_convention(sym_store, new_address)
                self.add_to_be_verified_functions()
                utils.output_logger.info('Function ' + verified_func_name + ' is verified at specific path under above-mentioned assumptions.\n')
        else:
            # NUM_OF_NEGATIVES
            self.cmc_func_exec_info[verified_func_name][2] += 1
        utils.logger.info('The symbolic execution has been terminated at the path\n')


    def handle_unbounded_jump_table_w_tb(self, trace_list, src_names, boundary, blk):
        trace_list = trace_list[::-1]
        src_name = src_names[0]
        src_len = utils.get_sym_length(src_name)
        rip = blk.sym_store.rip
        src_sym = sym_engine.get_sym(blk.sym_store.store, rip, src_name, src_len)
        cjmp_blk_idx, jt_idx_upperbound = cfg_helper.gen_jt_idx_upperbound(trace_list, boundary)
        if not jt_idx_upperbound: return -1
        jt_assign_blk_idx, is_jt_assign_inst = cfg_helper.check_jump_table_assign_inst(trace_list, cjmp_blk_idx)
        if not is_jt_assign_inst: return -1
        jt_assign_blk = trace_list[jt_assign_blk_idx]
        distinct_entries, inst_dest, src_len = cfg_helper.get_distinct_jt_entries(jt_assign_blk, src_sym, jt_idx_upperbound, self.block_set)
        if not distinct_entries: return -1
        sym_store_list = cfg_helper.reconstruct_jt_sym_stores(jt_assign_blk, distinct_entries, inst_dest, src_len)
        dest, target_addresses = cfg_helper.reconstruct_jt_target_addresses(trace_list, jt_assign_blk_idx, sym_store_list, self.address_jt_entries_map)
        if not target_addresses: return -1
        utils.logger.info(hex(trace_list[-1].address) + ': jump addresses resolved using jump table [' + ', '.join(map(lambda x: hex(sym_helper.int_from_sym(x)), target_addresses)) + ']')
        self._reconstruct_jump_targets(trace_list[-1], dest, target_addresses)
        return 0


    def retrieve_call_func_invariants(self, trace_list, src_names):
        for blk in trace_list:
            if blk.inst.startswith('call '):
                _, indoubt_arguments, invariant_arguments = self.get_func_call_invariant_arguments(blk, src_names)
                if not invariant_arguments: return -1
                if indoubt_arguments: return -1
                func_name, _ = cfg_helper.retrieve_internal_call_inst_func_name(blk, self.address_inst_map, self.address_sym_table)
                if func_name:
                    self.invariant_argument_map[func_name] = invariant_arguments


    def handle_symbolized_mem_w_tb(self, trace_list, src_names, rest):
        trace_list = trace_list[::-1]
        func_call_blk = trace_list[0]
        parent_blk, indoubt_arguments, invariant_arguments = self.get_func_call_invariant_arguments(func_call_blk, src_names)
        if not invariant_arguments: return -1
        if indoubt_arguments: return -1
        func_name, new_address = cfg_helper.retrieve_call_inst_func_name(func_call_blk, self.address_inst_map, self.address_sym_table)
        if func_name:
            self.invariant_argument_map[func_name] = invariant_arguments
        self._reconstruct_func_call_w_invariant_arguments(trace_list, parent_blk, invariant_arguments, func_name, new_address, rest)
        return 0


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
                # print(last_constraint)
                if last_constraint:
                    predicates = last_constraint.get_predicates()
                    m = sym_helper.check_pred_satisfiable(predicates)
                    if m is not False:
                        stack_val_len = self.mem_len_map[stack_addr]
                        stack_val = sym_engine.get_sym(tmp_sym_store.store, tmp_sym_store.rip, '[' + stack_addr + ']', stack_val_len)
                        res = stack_val
                        for d in m.decls():
                            s_val = m[d]
                            s_len = s_val.size()
                            res = sym_helper.substitute_sym_val(res, sym_helper.bit_vec_wrap(d.name(), s_len), s_val)
                            substitute_pair.append((sym_helper.bit_vec_wrap(d.name(), s_len), s_val))
                        sym_engine.set_sym(tmp_sym_store.store, tmp_sym_store.rip, '[' + stack_addr + ']', res)
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
        

    def tb_src_is_binary_sym(self, src_names):
        res = False
        if len(src_names) == 1:
            src_name = src_names[0]
            if utils.imm_start_pat.match(src_name):
                mem_addr = utils.imm_str_to_int(src_name)
                if mem_addr in self.address_sym_table:
                    res = True
        return res


    def trace_back(self, blk, sym_names, trace_list, tb_type):
        utils.logger.info('trace back')
        for _ in range(utils.MAX_TRACEBACK_COUNT):
            if blk.parent_no in self.block_set:
                p_store = self.block_set[blk.parent_no].sym_store.store
            else:
                if blk.inst.startswith('cmp'):
                    p_store = blk.sym_store.store
                else:
                    return -1, sym_names
            # p_store = self.block_set[blk.parent_no].sym_store.store
            src_names, need_stop, boundary, still_tb, func_call_point, rest, mem_len_map = semantics_traceback.parse_sym_src(self.address_sym_table, p_store, blk.sym_store.rip, blk.inst, sym_names, tb_type)
            self.mem_len_map.update(mem_len_map)
            utils.logger.info(hex(blk.address) + ': ' + blk.inst)
            utils.logger.info(src_names)
            # is_src_binary_sym = self.tb_src_is_binary_sym(src_names)
            # if is_src_binary_sym:
            #     return -2, src_names
            if func_call_point:
                trace_list.append(blk)
                if self.last_sym_memaddr_tb_inst_address:
                    if self.last_sym_memaddr_tb_inst_address == blk.address:
                        return -2, src_names
                    else:
                        self.last_sym_memaddr_tb_inst_address = blk.address
                else:
                    self.last_sym_memaddr_tb_inst_address = blk.address
                self.retrieve_call_func_invariants(trace_list, src_names)
                res = self.handle_symbolized_mem_w_tb(trace_list, src_names, rest)
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
        return -1, sym_names


    def jump_to_block(self, block, new_address, sym_store, constraint):
        new_inst = self.address_inst_map[new_address]
        self.add_new_block(block, new_address, new_inst, sym_store, constraint)
            

    def jump_to_dummy(self, block):
        block.add_to_children_list(self.dummy_block.block_no)
        

    def _add_block_based_on_predicate(self, parent_blk, address, inst, sym_store, constraint, rip, pred):
        sym_store = Sym_Store(sym_store.store, rip)
        semantics.cmov(sym_store.store, rip, inst, pred)
        self._add_new_block(parent_blk, address, inst, sym_store, constraint)


    def add_new_block(self, parent_blk, address, inst, sym_store, constraint):
        rip = cfg_helper.get_next_address(address, self.address_next_map, self.address_sym_table)
        if inst.startswith('bnd '):
            inst = inst.strip().split(' ', 1)[1]
        if inst.startswith('cmov'):
            prefix = 'cmov'
            res = smt_helper.parse_predicate(sym_store.store, inst, True, prefix)
            if res == True:
                self._add_block_based_on_predicate(parent_blk, address, inst, sym_store, constraint, rip, True)
            elif res == False:
                self._add_block_based_on_predicate(parent_blk, address, inst, sym_store, constraint, rip, False)
            else:
                self._add_block_based_on_predicate(parent_blk, address, inst, sym_store, constraint, rip, True)
                self._add_block_based_on_predicate(parent_blk, address, inst, sym_store, constraint, rip, False)
        else:
            sym_store = Sym_Store(sym_store.store, rip, inst)
            self._add_new_block(parent_blk, address, inst, sym_store, constraint)


    def _add_new_block(self, parent_blk, address, inst, sym_store, constraint):
        if inst.startswith('bnd '):
            inst = inst.strip().split(' ', 1)[1]
        if sym_store.store[lib.NEED_TRACE_BACK]:
            trace_list = []
            inst_split = inst.strip().split(' ', 1)
            inst_args = utils.parse_inst_args(inst_split)
            utils.logger.info(inst_args[0])
            self.mem_len_map = {}
            new_srcs, _ = smt_helper.get_bottom_source(inst_args[0], sym_store.store, sym_store.rip, self.mem_len_map)
            res, sym_names = self.trace_back(parent_blk, new_srcs, trace_list, TRACE_BACK_TYPE.SYMBOLIC)
            if res == -1:
                if constraint is not None:
                    res = cfg_helper.check_path_reachability(constraint)
                    if res == False:
                        return
                    else:
                        tmp = hex(address) + ': ' + inst
                        utils.output_logger.info('The path is unsound due to unresolved symbolic memory address at ' + tmp + '\n')
                if 'rdi' in sym_names:
                    utils.output_logger.info('The path is unsound due to the existence of argc\n')
            elif res == -2:
                sym_name = sym_names[0]
                mem_addr = utils.imm_str_to_int(sym_name)
                bin_sym_name = self.address_sym_table[mem_addr][0]
                utils.logger.info('The path is unsound due to undetermined symbolic memory address at ' + bin_sym_name + ' in the original binary file\n')
                utils.output_logger.info('The path is unsound due to undetermined symbolic memory address at ' + bin_sym_name + ' in the original binary file\n')
                # utils.logger.info('Cannot trace back to the internal/external function that causes the issue')
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
            # if smt_helper.is_inst_aff_flag(sym_store.store, sym_store.rip, address, inst):
            #     self.aff_flag_inst = (inst, sym_store)
            self.block_stack.append(block)


    def add_new_constraint(self, store, constraint, inst, val, prefix='j'):
        new_constraint = constraint
        pred_expr = smt_helper.parse_predicate(store, inst, val, prefix)
        if pred_expr != None:
            new_constraint = Constraint(constraint, pred_expr)
        return new_constraint


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


    def draw_cfg(self, start_block):
        block_set = []
        res = 'digraph cfg {\n'
        res += '    node [shape=record];\n'
        block_set.append(start_block)
        visited_block = []
        while block_set:
            block = self.block_stack.pop()
            if block not in visited_block:
                res += block.draw()
                res += block.draw_edge()
                children_list = block.children_blk_list
                for blk_no in children_list:
                    block_set.append(self.block_set[blk_no])
                visited_block.append(block)
        res += '}'
        with open('cfg.dot', 'w+') as f:
            f.write(res)
        utils.convert_dot_to_png('cfg')


    def reachable_addresses_num(self):
        res = len(list(self.address_block_map.keys()))
        return res
            
