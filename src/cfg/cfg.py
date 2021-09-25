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

import os

from ..common import utils
from ..common import lib
from ..common.lib import TRACE_BACK_RET_TYPE
from .block import Block
from .constraint import Constraint
from .sym_store import Sym_Store
from . import trace_back
from . import cfg_helper
from ..semantics import semantics
from ..semantics import semantics_tb_sym
from ..semantics import semantics_tb_indirect
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
        self.external_lib_assumptions = {}
        self.external_mem_preservation = []
        self.sym_valueset_map = {}
        # Reconstruct the flow path with the following parent block no and new presumptions
        self.function_inedges_map = {}
        self.function_inedges_map['_start'] = {}
        self.function_inedges_map['main'] = {}
        self.function_inedges_map['main']['_start'] = []
        sym_store = Sym_Store(None, None)
        sym_store.store[lib.VERIFIED_FUNC_INFO] = (start_address, func_name)
        self.cmc_exec_info = [0] * utils.CMC_EXEC_RES_COUNT
        self.func_call_order = ['_start', 'main']
        self.func_start_addr_name_map = {}
        constraint = None
        sym_helper.cnt_init()
        cfg_helper.start_init(sym_store.store, start_address, utils.INIT_BLOCK_NO)
        cfg_helper.cfg_init_parameter(sym_store.store, self.sym_table)
        self.build_cfg(start_address, sym_store, constraint)
        # self.pp_unreachable_instrs()

    
    def build_cfg(self, start_address, sym_store, constraint):
        start_inst = self.address_inst_map[start_address]
        utils.logger.debug(sym_store.pp_store())
        self.add_new_block(None, start_address, start_inst, sym_store, constraint)
        while self.block_stack:
            curr = self.block_stack.pop()
            utils.logger.debug('Block no is: %s' % (curr.block_id))
            if curr.parent_id is not None:
                utils.logger.debug('Parent no is: %s' % (curr.parent_id))
            utils.logger.debug('MEM polluted:%s' % (curr.sym_store.store[lib.MEM_CONTENT_POLLUTED]))
            utils.logger.debug('%s: %s' % (hex(curr.address), curr.inst))
            utils.logger.debug(curr.sym_store.pp_store())
            address, inst, sym_store, constraint = curr.address, curr.inst, curr.sym_store, curr.constraint
            if inst and inst.startswith('bnd '):
                inst = inst.strip().split(' ', 1)[1]
            if utils.check_branch_inst(inst):
                self.construct_branch(curr, address, inst, sym_store, constraint)
            else:
                new_address = cfg_helper.get_next_address(address, self.address_next_map, self.address_sym_table)
                if new_address != -1:
                    self.jump_to_block(curr, new_address, sym_store, constraint)
            

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
        new_inst = self.address_inst_map[new_address]
        self.add_new_block(block, new_address, new_inst, sym_store, new_constraint)
        

    def construct_branch(self, block, address, inst, sym_store, constraint):
        if inst == 'ret' or inst.endswith(' ret'):
            self.build_ret_branch(block, address, sym_store, constraint)
        else:
            jump_address_str = inst.split(' ', 1)[1].strip()
            new_address = smt_helper.get_jump_address(sym_store.store, sym_store.rip, jump_address_str)
            if new_address in self.address_inst_map:
                new_func_name = self._update_function_inedges_for_internal_call(sym_store, inst, new_address)
                self.handle_internal_jumps(block, address, inst, sym_store, constraint, new_address, new_func_name)
            elif new_address in self.address_sym_table:
                ext_func_name = cfg_helper.get_function_name_from_addr_sym_table(self.address_sym_table, new_address)
                self.handle_external_function(new_address, ext_func_name, block, address, inst, sym_store, constraint)
            elif sym_helper.sym_is_int_or_bitvecnum(new_address):
                ext_func_name = 'undefined'
                self.handle_external_function(new_address, ext_func_name, block, address, inst, sym_store, constraint)
                utils.logger.debug('Jump to an undefined external address ' + str(new_address) + ' at address ' + hex(address))
            elif str(new_address).startswith(utils.MEM_DATA_SEC_SUFFIX):
                ext_func_name = str(new_address)
                self.handle_external_function(new_address, ext_func_name, block, address, inst, sym_store, constraint)
                utils.logger.debug('Jump to an undefined external address ' + str(new_address) + ' at address ' + hex(address))
            else:
                self.handle_unresolved_indirect_jumps(block, address, inst, constraint, new_address)
                

    def handle_internal_jumps(self, block, address, inst, sym_store, constraint, new_address, new_func_name):
        utils.logger.info(hex(address) + ': jump address is ' + sym_helper.string_of_address(new_address))
        if utils.check_not_single_branch_inst(inst):    # je xxx
            self.construct_conditional_branches(block, address, inst, new_address, sym_store, constraint)
        else:
            if new_address in self.address_block_map and new_address in self.address_sym_table and new_address in self.ret_call_address_map.values():
                if self._explored_func_block(sym_store, new_address):
                    func_name = cfg_helper.get_function_name_from_addr_sym_table(self.address_sym_table, new_address)
                    self.build_ret_branch(block, new_address, sym_store, constraint)
                    # self.handle_external_function(new_address, func_name, block, address, inst, sym_store, constraint)
                else:
                    if inst.startswith('call '):
                        sym_store.store[lib.VERIFIED_FUNC_INFO] = (new_address, new_func_name)
                    self.jump_to_block(block, new_address, sym_store, constraint)
            else:
                if inst.startswith('call '):
                    sym_store.store[lib.VERIFIED_FUNC_INFO] = (new_address, new_func_name)
                self.jump_to_block(block, new_address, sym_store, constraint)


    def handle_external_function(self, ext_func_address, ext_func_name, block, address, inst, sym_store, constraint):
        rip, store = sym_store.rip, sym_store.store
        inv_names = self.external_lib_assumptions.get(ext_func_address, [])
        if ext_func_name.startswith('__libc_start_main'):
            semantics.call_op(store, rip, block.block_id)
            next_address = self.main_address
            next_function = 'main'
            self.func_start_addr_name_map[self.main_address] = next_function
            utils.logger.info(hex(address) + ': jump address is ' + sym_helper.string_of_address(next_address))
            sym_store.store[lib.VERIFIED_FUNC_INFO] = (next_address, next_function)
            ext_handler.ext__libc_start_main(store, rip, self.main_address, block.block_id, inv_names)
            self.jump_to_block(block, next_address, sym_store, constraint)
        elif ext_func_name.startswith('pthread_create'):
            self._cfg_create_new_thread(ext_func_address, ext_func_name, block, address, inst, sym_store, constraint, inv_names)
        elif ext_func_name.startswith(('malloc', 'calloc', 'realloc')):
            ext_name = ext_func_name.split('@', 1)[0].strip()
            heap_addr = sym_store.store[lib.HEAP_ADDR]
            new_heap_addr = ext_handler.ext_alloc_mem_call(store, rip, heap_addr, ext_name, block.block_id, inv_names)
            sym_store.store[lib.HEAP_ADDR] = new_heap_addr
            self.build_ret_branch(block, address, sym_store, constraint)
        elif ext_func_name.startswith(('free')):
            ext_handler.ext_free_mem_call(store, rip)
            self.build_ret_branch(block, address, sym_store, constraint)
        else:
            mem_preserve_assumption = True if ext_func_address in self.external_mem_preservation else False
            ext_handler.ext_func_call(store, rip, block.block_id, inv_names, mem_preserve_assumption)
            ext_name = ext_func_name.split('@', 1)[0].strip()
            if ext_name not in lib.TERMINATION_FUNCTIONS:
                self.build_ret_branch(block, address, sym_store, constraint)
            else:
                utils.logger.info('The symbolic execution has been terminated at the path due to the call of the function ' + ext_name + '\n')
                

    def handle_unresolved_indirect_jumps(self, block, address, inst, constraint, new_address):
        if inst.startswith('jmp ') and not inst.endswith(']'):
            trace_list = []
            if block.address in self.address_jt_entries_map:
                inst_dest, target_addresses = self.address_jt_entries_map[block.address]
                self._reconstruct_new_branches(block, inst_dest, target_addresses)
                res = lib.TRACE_BACK_RET_TYPE.JT_SUCCEED
            else:
                res, _ = self.trace_back(block, [inst.split(' ', 1)[1].strip()], trace_list)
            if res != lib.TRACE_BACK_RET_TYPE.JT_SUCCEED:
                if constraint is not None:
                    path_reachable = cfg_helper.check_path_reachability(constraint)
                    if path_reachable == False: return
                utils.logger.info('Cannot resolve the jump address ' + sym_helper.string_of_address(new_address) + ' of ' + inst + ' at address ' + hex(address))
                utils.logger.info(trace_back.pp_tb_debug_info(res, address, inst))
                # sys.exit('Cannot resolve the jump address ' + sym_helper.string_of_address(new_address) + ' of ' + inst + ' at address ' + hex(address))
        else:
            if constraint is not None:
                path_reachable = cfg_helper.check_path_reachability(constraint)
                if path_reachable == False: 
                    utils.logger.info('The path is infeasible at the jump address ' + sym_helper.string_of_address(new_address) + ' of ' + inst + ' at address ' + hex(address) + '\n')
                    return
            utils.logger.info('Cannot resolve the jump address ' + sym_helper.string_of_address(new_address) + ' of ' + inst + ' at address ' + hex(address))
            # sys.exit('Cannot resolve the jump address ' + sym_helper.string_of_address(new_address) + ' of ' + inst + ' at address ' + hex(address))


    def build_ret_branch(self, block, address, sym_store, constraint):
        block_id = None
        new_address = semantics.ret(sym_store.store, block.block_id)
        if new_address != None:
            if sym_helper.sym_is_int_or_bitvecnum(new_address):
                utils.logger.info(hex(address) + ': the return address is {}'.format(hex(new_address)))
                if new_address in self.address_inst_map:
                    if new_address not in self.ret_call_address_map:
                        call_target = self._get_prev_inst_target(new_address)
                        if call_target:
                            self.ret_call_address_map[new_address] = call_target
                    new_func_name = cfg_helper.find_out_func_name_with_addr_in_range(self.func_start_addr_name_map, new_address)
                    sym_store.store[lib.VERIFIED_FUNC_INFO] = (new_address, new_func_name)
                    block_id = self.jump_to_block(block, new_address, sym_store, constraint)
                else:
                    self.jump_to_dummy(block)
            elif sym_helper.is_term_address(new_address):
                self.jump_to_dummy(block)
                self.handle_cmc_path_termination(block, sym_store, new_address)
            else:
                if constraint is not None:
                    path_reachable = cfg_helper.check_path_reachability(constraint)
                    if path_reachable == False: return
                # utils.logger.info('Cannot resolve the return address of ' + inst + ' at address ' + hex(address))
                # sys.exit('Cannot resolve the return address of ' + inst + ' at address ' + hex(address))
            return block_id

    def handle_cmc_path_termination(self, block, sym_store, new_address):
        verified_func_start_addr, verified_func_name = sym_store.store[lib.VERIFIED_FUNC_INFO]
        # NUM_OF_PATHS
        self.cmc_exec_info[0] += 1
        if sym_store.store[lib.POINTER_RELATED_ERROR]:
            # NUM_OF_NEGATIVES
            self.cmc_exec_info[2] += 1
            self._update_pointer_related_error_info(sym_store.store)
        else:
            # NUM_OF_POSITIVES
            self.cmc_exec_info[1] += 1
            # Sound cases
            self.cmc_exec_info[7] += 1
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
        self._reconstruct_new_branches(trace_list[-1], dest, target_addresses)
        return lib.TRACE_BACK_RET_TYPE.JT_SUCCEED


    def trace_back_sym_addr(self, blk, sym_names):
        utils.logger.info('trace back for symbolized memory address')
        print('trace back for symbolized memory address')
        sym_store = blk.sym_store
        store, rip = sym_store.store, sym_store.rip
        tb_halt_point = False
        count, blockid_sym_list = 0, []
        src_names = None
        init_state_sym_names = []
        smallest_block_id, restart_address, restart_inst, restart_block_id = blk.block_id, None, None, None
        blockid_sym_list, _ = self._update_blockid_sym_list(blockid_sym_list, store, rip, sym_names)
        sorted(blockid_sym_list, key=lambda bn_pair: bn_pair[0])
        print(blockid_sym_list)
        while blockid_sym_list and count < utils.MAX_TRACEBACK_COUNT:
            curr_block_id, curr_sym_name = blockid_sym_list.pop()
            if curr_block_id != -1:
                curr_blk = self.block_set[curr_block_id]
                print(curr_block_id)
                curr_store, curr_rip, curr_address, curr_inst = curr_blk.sym_store.store, curr_blk.sym_store.rip, curr_blk.address, curr_blk.inst
                print(curr_inst)
                p_block_id, p_sym_store = self._get_parent_block_info(curr_blk)
                print('parent block no')
                print(p_block_id)
                if p_sym_store is None:
                    return lib.TRACE_BACK_RET_TYPE.TB_PARENT_BLOCK_DOES_NOT_EXIST
                print('parse semantics to tb')
                src_names, still_tb, func_call_point, _, mem_len_map = semantics_tb_sym.parse_sym_src(self.address_sym_table, self.address_inst_map, p_sym_store.store, curr_rip, curr_inst, [curr_sym_name])
                print(src_names)
                self.mem_len_map.update(mem_len_map)
                utils.logger.info(hex(curr_blk.address) + ': ' + curr_blk.inst)
                utils.logger.info(src_names)
                print(func_call_point)
                print(still_tb)
                if func_call_point:
                    if smallest_block_id > curr_block_id:
                        print('func call point')
                        smallest_block_id = curr_block_id
                        restart_address = curr_address
                        restart_inst = curr_inst
                        restart_block_id = p_block_id
                        restart_sym_store = p_sym_store
                    self._update_external_assumptions(curr_store, curr_rip, curr_inst, src_names)
                elif still_tb:
                    pass
                else: 
                    utils.logger.info('\n')
                    break
                print(src_names)
                print(blockid_sym_list)
                if not func_call_point:
                    blockid_sym_list, tmp_res = self._update_blockid_sym_list(blockid_sym_list, p_sym_store.store, curr_rip, src_names)
                    if not tmp_res:
                        return lib.TRACE_BACK_RET_TYPE.SYMADDR_UNINITIALIZED_MEM_CONTENT
                if trace_back.reach_traceback_halt_point(blockid_sym_list):
                    print('_reach_traceback_halt_point')
                    print(blockid_sym_list)
                    tb_halt_point = True
                    self._update_external_assumptions(curr_store, curr_rip, curr_inst, src_names)
                    break
            else:
                if src_names:
                    init_state_sym_names.extend(src_names)
            count += 1
        res = self._handle_trace_back_results(tb_halt_point, count, blockid_sym_list, restart_address, restart_inst, restart_block_id, restart_sym_store)
        return res


    def _handle_trace_back_results(self, tb_halt_point, count, blockid_sym_list, restart_address, restart_inst, restart_block_id, restart_sym_store):
        if tb_halt_point:
            block_id, sym_name = blockid_sym_list[0]
            print('tb_halt_point')
            self._remove_all_children_block(block_id)
            restart_block = self.block_set[block_id]
            alternative_sym = 'rdi'
            alternative_values = trace_back.generate_alternative_values(alternative_sym)
            self._reconstruct_new_branches(restart_block, alternative_sym, alternative_values)
            # self.add_new_block(self.block_set[restart_block_id], restart_address, restart_inst, restart_sym_store, self.block_set[restart_block_id].constraint)
            return lib.TRACE_BACK_RET_TYPE.SYMADDR_SUCCEED
        elif count != utils.MAX_TRACEBACK_COUNT:
            print('restart construction')
            print(restart_block_id)
            print(restart_address)
            print(restart_inst)
            self._remove_all_children_block(restart_block_id)
            self.add_new_block(self.block_set[restart_block_id], restart_address, restart_inst, restart_sym_store, self.block_set[restart_block_id].constraint)
            return lib.TRACE_BACK_RET_TYPE.SYMADDR_SUCCEED
        else:
            return lib.TRACE_BACK_RET_TYPE.UNRESOLVED


    def _update_external_assumptions(self, store, rip, inst, src_names):
        jump_address_str = inst.split(' ', 1)[1].strip()
        new_address = smt_helper.get_jump_address(store, rip, jump_address_str)
        self.external_lib_assumptions[new_address] = src_names
        if new_address not in self.external_mem_preservation:
            for src_name in src_names:
                if utils.imm_start_pat.match(src_name):
                    self.external_mem_preservation.append(new_address)



    def _update_blockid_sym_list(self, blockid_sym_list, p_store, rip, src_names):
        res = True
        print('_update_blockid_sym_list')
        print(blockid_sym_list)
        print(src_names)
        for sym_name in src_names:
            tmp_name = sym_name
            if utils.imm_start_pat.match(sym_name):
                tmp_name = '[' + sym_name + ']'
            b_id = sym_engine.get_sym_block_id(p_store, rip, tmp_name)
            if b_id:
                blockid_sym_list = self._add_new_b_id_sym_pair(blockid_sym_list, b_id, sym_name)
            else:
                res = False
                utils.logger.info('The symbolic memory address directly comes from ' + tmp_name)
        return blockid_sym_list, res


    def _add_new_b_id_sym_pair(self, blockid_sym_list, b_id, sym_name):
        if isinstance(b_id, int):
            blockid_sym_list.append((b_id, sym_name))
        else:
            sym_name_split = sym_name.split(':')
            blockid_sym_list.append((b_id[0], sym_name_split[0]))
            blockid_sym_list.append((b_id[1], sym_name_split[1]))
        return blockid_sym_list


    def _get_parent_block_info(self, blk):
        block_id, sym_store = None, None
        if blk.parent_id in self.block_set:
            parent_block = self.block_set[blk.parent_id]
            block_id, sym_store = parent_block.block_id, parent_block.sym_store
        return block_id, sym_store


    def _get_parent_store(self, blk):
        store = None
        if blk.parent_id in self.block_set:
            parent_block = self.block_set[blk.parent_id]
            store = parent_block.sym_store.store
        else:
            if blk.inst.startswith('cmp'):
                store = blk.sym_store.store
        return store
            

    def trace_back(self, blk, sym_names, trace_list):
        utils.logger.info('trace back')
        for _ in range(utils.MAX_TRACEBACK_COUNT):
            p_store = self._get_parent_store(blk)
            if p_store is None:
                return lib.TRACE_BACK_RET_TYPE.TB_PARENT_BLOCK_DOES_NOT_EXIST, sym_names
            src_names, need_stop, boundary, still_tb, mem_len_map = semantics_tb_indirect.parse_sym_src(p_store, blk.sym_store.rip, blk.inst, sym_names)
            self.mem_len_map.update(mem_len_map)
            utils.logger.info(hex(blk.address) + ': ' + blk.inst)
            utils.logger.info(src_names)
            if need_stop and len(src_names) == 1:
                res = self.handle_unbounded_jump_table_w_tb(trace_list, src_names, boundary, blk)
                return res, src_names
            elif still_tb:
                trace_list.append(blk)
                blk = self.block_set[blk.parent_id]
                sym_names = src_names
            else: 
                utils.logger.info('\n')
                break
        return lib.TRACE_BACK_RET_TYPE.UNRESOLVED, sym_names


    def jump_to_block(self, block, new_address, sym_store, constraint):
        new_inst = self.address_inst_map[new_address]
        block_id = self.add_new_block(block, new_address, new_inst, sym_store, constraint)
        return block_id


    def jump_to_dummy(self, block):
        block.add_to_children_list(self.dummy_block.block_id)
        

    def add_new_block(self, parent_blk, address, inst, sym_store, constraint):
        rip = cfg_helper.get_next_address(address, self.address_next_map, self.address_sym_table)
        if inst.startswith('bnd '):
            inst = inst.strip().split(' ', 1)[1]
        if inst.startswith('cmov'):
            block_id = self._add_new_block_w_cmov_inst(parent_blk, address, inst, sym_store, constraint, rip)
        else:
            sym_store = Sym_Store(sym_store.store, rip)
            block_id = self._add_new_block(parent_blk, address, inst, sym_store, constraint)
        return block_id


    def _add_new_block(self, parent_blk, address, inst, sym_store, constraint, update_sym_store=True):
        block_id = None
        if inst.startswith('bnd '):
            inst = inst.strip().split(' ', 1)[1]
        parent_id = parent_blk.block_id if parent_blk is not None else None
        block = Block(parent_id, address, inst.strip(), sym_store, constraint)
        block_id = block.block_id
        if update_sym_store and inst and not utils.check_branch_inst_wo_call(inst) and not inst.startswith('cmov'):
            semantics.parse_semantics(sym_store.store, sym_store.rip, inst, block_id)
        if sym_store.store[lib.NEED_TRACE_BACK]:
            self._handle_symbolized_mem_addr_w_traceback(parent_blk, address, inst, sym_store, constraint)
        elif sym_store.store[lib.POINTER_RELATED_ERROR]:
            self._terminate_path_w_pointer_related_errors(sym_store.store, address, inst)
        else:
            self.block_set[block_id] = block
            if parent_blk:
                parent_blk.add_to_children_list(block_id)
            if address in self.address_block_map:
                self.address_block_map[address].append(block)
            else:
                self.address_block_map[address] = [block]
            self.block_stack.append(block)
        return block_id

        
    def add_new_constraint(self, store, constraint, inst, val, prefix='j'):
        new_constraint = constraint
        pred_expr = smt_helper.parse_predicate(store, inst, val, prefix)
        if pred_expr != None:
            new_constraint = Constraint(constraint, pred_expr)
        return new_constraint


    def _handle_symbolized_mem_addr_w_traceback(self, parent_blk, address, inst, sym_store, constraint):
        inst_split = inst.strip().split(' ', 1)
        inst_args = utils.parse_inst_args(inst_split)
        utils.logger.info(inst_args[0])
        self.mem_len_map = {}
        new_srcs, _ = smt_helper.get_bottom_source(inst_args[0], sym_store.store, sym_store.rip, self.mem_len_map)
        res = self.trace_back_sym_addr(parent_blk, new_srcs)
        if res != lib.TRACE_BACK_RET_TYPE.SYMADDR_SUCCEED:
            if constraint is not None:
                path_reachable = cfg_helper.check_path_reachability(constraint)
                if path_reachable == False: return
            utils.logger.info(trace_back.pp_tb_debug_info(res, address, inst))
            utils.output_logger.info(trace_back.pp_tb_debug_info(res, address, inst))
            # Unresolved symbolic memory address
            self.cmc_exec_info[6] += 1


    def _terminate_path_w_pointer_related_errors(self, store, address, inst):
        utils.output_logger.info('Pointer-related error at ' + hex(address) + ': ' + inst + '\n')
        # NUM_OF_PATHS
        self.cmc_exec_info[0] += 1
        # NUM_OF_NEGATIVES
        self.cmc_exec_info[2] += 1
        self._update_pointer_related_error_info(store)


    def _update_function_inedges_for_internal_call(self, sym_store, inst, new_address):
        new_func_name = ''
        if inst.startswith('call '):
            _, curr_func_name = sym_store.store[lib.VERIFIED_FUNC_INFO]
            new_func_name = cfg_helper.get_function_name_from_addr_sym_table(self.address_sym_table, new_address)
            self.func_start_addr_name_map[new_address] = new_func_name
            if '@' not in new_func_name:
                if new_func_name not in self.func_call_order:
                    self.func_call_order.append(new_func_name)
            if new_func_name not in self.function_inedges_map:
                self.function_inedges_map[new_func_name] = {}
            self.function_inedges_map[new_func_name][curr_func_name] = []
        return new_func_name
        

    def _add_new_block_w_cmov_inst(self, parent_blk, address, inst, sym_store, constraint, rip):
        block_id = None
        prefix = 'cmov'
        res = smt_helper.parse_predicate(sym_store.store, inst, True, prefix)
        if res == True:
            block_id = self._add_block_based_on_predicate(parent_blk, address, inst, sym_store, constraint, rip, True)
        elif res == False:
            block_id = self._add_block_based_on_predicate(parent_blk, address, inst, sym_store, constraint, rip, False)
        else:
            block_id = self._add_block_based_on_predicate(parent_blk, address, inst, sym_store, constraint, rip, True)
            block_id = self._add_block_based_on_predicate(parent_blk, address, inst, sym_store, constraint, rip, False)
        return block_id


    def _add_block_based_on_predicate(self, parent_blk, address, inst, sym_store, constraint, rip, pred):
        sym_store = Sym_Store(sym_store.store, rip)
        block_id = self._add_new_block(parent_blk, address, inst, sym_store, constraint)
        semantics.cmov(sym_store.store, rip, inst, pred, block_id)
        return block_id


    def _reconstruct_new_branches(self, blk, alternative_sym, alternative_values):
        address, inst = blk.address, blk.inst
        rip, store, constraint = blk.sym_store.rip, blk.sym_store.store, blk.constraint
        for val in alternative_values:
            new_sym_store = Sym_Store(store, rip)
            block_id = self._add_new_block(blk, address, inst, new_sym_store, constraint, False)
            sym_engine.set_sym(new_sym_store.store, rip, alternative_sym, val, block_id)


    def _update_pointer_related_error_info(self, store):
        if store[lib.POINTER_RELATED_ERROR] == lib.MEMORY_RELATED_ERROR_TYPE.NULL_POINTER_DEREFERENCE:
            self.cmc_exec_info[3] += 1
        elif store[lib.POINTER_RELATED_ERROR] == lib.MEMORY_RELATED_ERROR_TYPE.USE_AFTER_FREE:
            self.cmc_exec_info[4] += 1
        elif store[lib.POINTER_RELATED_ERROR] == lib.MEMORY_RELATED_ERROR_TYPE.BUFFER_OVERFLOW:
            self.cmc_exec_info[5] += 1


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
        new_sym_store = Sym_Store(sym_store.store, prev_sym_store.rip)
        res = new_sym_store.state_ith_eq(prev_sym_store) and new_sym_store.aux_mem_eq(prev_sym_store, lib.AUX_MEM)
        return res


    def _remove_all_children_block(self, p_block_id):
        block_id_list = []
        block_id_stack = [p_block_id]
        p_block = self.block_set[p_block_id]
        while block_id_stack:
            curr_block_id = block_id_stack.pop()
            curr_block = self.block_set[curr_block_id]
            children_block_list = curr_block.children_blk_list
            for children_block_id in children_block_list:
                if children_block_id != curr_block_id and children_block_id != -1:
                    if children_block_id not in block_id_list:
                        block_id_list.append(children_block_id)
                        block_id_stack.append(children_block_id)
        sorted(block_id_list, reverse=True)
        for block_id in block_id_list:
            block = self.block_set[block_id]
            address = block.address
            if address in self.address_block_map:
                del self.address_block_map[address]
            del self.block_set[block_id]
            if block in self.block_stack:
                self.block_stack.remove(block)
        p_block.children_blk_list = []


    def _cfg_create_new_thread(self, ext_func_address, ext_func_name, block, address, inst, sym_store, constraint, inv_names):  
        store, rip = sym_store.store, sym_store.rip
        jmp_sym_store = Sym_Store(store, rip)
        sym_rdi = sym_engine.get_sym(store, rip, 'rdi')
        if sym_helper.sym_is_int_or_bitvecnum(sym_rdi):
            semantics.ret(jmp_sym_store.store, block.block_id)
            rdi_val = sym_helper.int_from_sym(sym_rdi)
            if rdi_val in self.address_inst_map:
                utils.logger.info(hex(address) + ': jump address is ' + sym_helper.string_of_address(rdi_val))
                self.jump_to_block(block, rdi_val, jmp_sym_store, constraint)
        fall_through_sym_store = Sym_Store(store, rip)
        mem_preserve_assumption = True if ext_func_address in self.external_mem_preservation else False
        ext_handler.ext_func_call(fall_through_sym_store.store, fall_through_sym_store.rip, block.block_id, inv_names, mem_preserve_assumption)
        self.build_ret_branch(block, address, fall_through_sym_store, constraint)  
        

    def draw_callgraph(self, file_path):
        res = 'digraph callgraph {\n'
        res += '    node [shape=record];\n'
        for name in self.function_inedges_map:
            if name not in self.func_call_order:
                self.func_call_order.append(name)
        for name in self.func_call_order:
            res += self.draw_block(name)
        res += '\n'
        res += self.draw_demonstration()
        res += self.pp_pointer_related_error_info()
        for name, in_edge_map in self.function_inedges_map.items():
            res += self.draw_edges(name, in_edge_map)
        res += '}'
        with open(file_path + '.dot', 'w+') as f:
            f.write(res)
        utils.convert_dot_to_png(file_path)


    def draw_block(self, name):
        res = '    ' + utils.replace_dot_in_func_name(name) 
        res += ' [label=<<table border="0" cellspacing="0">'
        res += '<tr><td colspan="3">' + name + '</td></tr>'
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


    def pp_pointer_related_error_info(self):
        res = '    error_info'
        res += ' [label=<<table border="0" cellspacing="0">'
        res += '<tr>'
        func_exec_info = self.cmc_exec_info
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
        res += '</table>>];\n'
        return res


    def _pp_specific_error_info(self, func_exec_info, index, color):
        res = ''
        res += '<td port="port' + str(index) + '" border="0" bgcolor="' + color + '">' + str(func_exec_info[index]) + '</td>'
        return res


    def draw_edges(self, name, in_edge_map):
        res = ''
        if in_edge_map:
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
        res += str(edge_label)
        res += '</td>\n</tr>'
        return res

    def reachable_addresses_num(self):
        res = len(list(self.address_block_map.keys()))
        return res
            
    
    def pp_unreachable_instrs(self):
        reachable_addresses = set(self.address_block_map.keys())
        inst_addresses = sorted(list(self.address_inst_map.keys()))
        utils.logger.info('\n')
        utils.logger.info(utils.LOG_UNREACHABLE_INDICATOR)
        for address in inst_addresses:
            if address not in reachable_addresses:
                utils.logger.info(hex(address) + ': ' + self.address_inst_map[address])
