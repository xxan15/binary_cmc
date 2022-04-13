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

import sys
from collections import deque

from ..common.inst_element import Inst_Elem
from ..common import utils
from ..common import lib
from ..common.lib import TRACE_BACK_RET_TYPE
from ..common.lib import Tree
from .block import Block
from .constraint import Constraint
from .sym_store import Sym_Store
from . import trace_back
from . import cfg_helper
from ..semantics import semantics
from ..semantics import semantics_tb_sym
from ..semantics import semantics_tb_memaddr
from ..semantics import semantics_tb_indirect
from ..semantics import smt_helper
from ..semantics import ext_handler
from ..symbolic import sym_helper
from ..symbolic import sym_engine


class CFG(object):
    def __init__(self, sym_table, address_sym_table, address_inst_map, address_next_map, start_address, main_address, func_name, address_ext_func_map, pre_constraint, dll_func_info):
        self.block_set = {}
        self.block_stack = deque()
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
        self.global_pre_constraint = pre_constraint
        self.ret_call_address_map = {}
        self.address_jt_entries_map = {}
        self.sym_addr_valueset_map = {}
        self.external_lib_assumptions = {}
        self.external_mem_preservation = []
        self.address_ext_func_map = address_ext_func_map
        self.dll_func_info = dll_func_info
        sym_store = Sym_Store(None, None)
        self.cmc_exec_info = [0] * utils.CMC_EXEC_RES_COUNT
        self.num_of_resolved_indirects = 0
        self.num_of_unresolved_indirects = 0
        constraint = None
        sym_helper.cnt_init()
        constraint = cfg_helper.start_init(sym_store.store, start_address, utils.INIT_BLOCK_NO)
        constraint = cfg_helper.handle_pre_constraint(sym_store.store, sym_store.rip, constraint, utils.INIT_BLOCK_NO, self.global_pre_constraint, self.external_lib_assumptions)
        cfg_helper.cfg_init_parameter(sym_store.store, self.sym_table)
        self.build_cfg(start_address, sym_store, constraint)
        self.pp_unreachable_instrs()

    
    def build_cfg(self, start_address, sym_store, constraint):
        start_inst = self.address_inst_map[start_address]
        self.add_new_block(None, start_address, start_inst, sym_store, constraint)
        while self.block_stack:
            curr = self.block_stack.popleft()
            utils.logger.debug('%s: %s' % (hex(curr.address), curr.inst))
            # utils.logger.debug(str(curr.block_id) + '\n' + curr.sym_store.pp_store())
            address, inst, sym_store, constraint = curr.address, curr.inst, curr.sym_store, curr.constraint
            if inst and inst.startswith('bnd '):
                inst = inst.strip().split(' ', 1)[1]
            if utils.check_branch_inst(inst):
                self.construct_branch(curr, address, inst, sym_store, constraint)
            else:
                self._jump_to_next_block(curr, address, sym_store, constraint)


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
            

    def construct_conditional_jump_block(self, block, address, inst, new_address, sym_store, constraint, val, need_new_constraint=True):
        utils.logger.debug('%s: %s' % (hex(address), inst))
        # self.jump_to_block_w_new_constraint(block, inst, new_address, sym_store, constraint, val, need_new_constraint)
        if address in self.address_block_map:
            if (address, new_address) in self.loop_trace_counter:
                counter = self.loop_trace_counter[(address, new_address)]
                if counter < utils.MAX_LOOP_COUNT:
                    self.loop_trace_counter[(address, new_address)] += 1
                    self.jump_to_block_w_new_constraint(block, inst, new_address, sym_store, constraint, val, need_new_constraint)
                else:
                    # self.loop_trace_counter[(address, new_address)] = 0
                    utils.logger.info('The path is terminated since the loop upperbound is hit')
                    self.handle_cmc_path_termination(sym_store.store)
            else:
                # self.loop_trace_counter[(address, new_address)] = 1
                # utils.logger.info('jump_to_block_w_new_constraint no in loop counter')
                exists_loop = cfg_helper.detect_loop(block, address, new_address, self.block_set)
                if exists_loop:
                    self.loop_trace_counter[(address, new_address)] = 1
                self.jump_to_block_w_new_constraint(block, inst, new_address, sym_store, constraint, val, need_new_constraint)
        else:
            # utils.logger.info('jump_to_block_w_new_constraint')
            self.jump_to_block_w_new_constraint(block, inst, new_address, sym_store, constraint, val, need_new_constraint)


    def jump_to_block_w_new_constraint(self, block, inst, new_address, sym_store, constraint, val, need_new_constraint=True):
        new_constraint = constraint
        if need_new_constraint:
            new_constraint = self.add_new_constraint(sym_store.store, constraint, inst, val)
        new_inst = self.address_inst_map[new_address]
        block_id = self.add_new_block(block, new_address, new_inst, sym_store, new_constraint)
        return block_id
        

    def construct_branch(self, block, address, inst, sym_store, constraint):
        if inst == 'ret' or inst.endswith(' ret') or inst.startswith('ret '):
            self.build_ret_branch(block, address, sym_store, constraint)
        else:
            jump_address_str = inst.split(' ', 1)[1].strip()
            new_address = smt_helper.get_jump_address(sym_store.store, sym_store.rip, jump_address_str)
            if new_address in self.address_inst_map:
                if new_address in self.address_ext_func_map:
                    ext_func_name = cfg_helper.get_function_name_from_addr_sym_table(self.address_sym_table, new_address)
                    self.handle_external_function(new_address, ext_func_name, block, address, inst, sym_store, constraint)
                else:
                    self.handle_internal_jumps(block, address, inst, sym_store, constraint, new_address)
            elif new_address in self.address_sym_table:
                ext_func_name = cfg_helper.get_function_name_from_addr_sym_table(self.address_sym_table, new_address)
                self.handle_external_function(new_address, ext_func_name, block, address, inst, sym_store, constraint)
            elif new_address in self.dll_func_info:
                ext_func_name = self.dll_func_info[new_address]
                self.handle_external_function(new_address, ext_func_name, block, address, inst, sym_store, constraint)
            elif sym_helper.sym_is_int_or_bitvecnum(new_address) or str(new_address).startswith(utils.MEM_DATA_SEC_SUFFIX):
                ext_func_name = str(new_address)
                self.handle_external_function(new_address, ext_func_name, block, address, inst, sym_store, constraint)
                utils.logger.debug('Jump to an undefined external address ' + str(new_address) + ' at address ' + hex(address))
            else:
                self.handle_unresolved_indirect_jumps(block, address, inst, constraint, new_address)
                

    def handle_internal_jumps(self, block, address, inst, sym_store, constraint, new_address):
        utils.logger.info(hex(address) + ': jump address is ' + sym_helper.string_of_address(new_address))
        if utils.check_not_single_branch_inst(inst):    # je xxx
            self.construct_conditional_branches(block, address, inst, new_address, sym_store, constraint)
        else:
            if new_address in self.address_block_map and new_address in self.ret_call_address_map.values(): # new_address in self.address_sym_table
                if self._explored_func_block(sym_store, new_address):
                    self.build_ret_branch(block, new_address, sym_store, constraint)
                else:
                    self.jump_to_block(block, new_address, sym_store, constraint)
            else:
                if inst.startswith('jmp '):
                    self.construct_conditional_jump_block(block, address, inst, new_address, sym_store, constraint, True, False)
                else:
                    self.jump_to_block(block, new_address, sym_store, constraint)


    def handle_external_function(self, ext_func_address, ext_func_name, block, address, inst, sym_store, constraint):
        rip, store, new_constraint = sym_store.rip, sym_store.store, constraint
        inv_names = self.external_lib_assumptions.get(ext_func_address, [])
        ext_name = ext_func_name.split('@', 1)[0].strip()
        pre_constraint = self.global_pre_constraint[ext_name] if ext_name in self.global_pre_constraint else None
        if ext_func_name.startswith('__libc_start_main'):
            semantics.call_op(store, rip, block.block_id)
            next_address = self.main_address
            ext_handler.ext__libc_start_main(store, rip, self.main_address, block.block_id, inv_names)
            new_constraint = cfg_helper.insert_new_constraints(store, rip, block.block_id, ext_name, pre_constraint, constraint)
            self.jump_to_block(block, next_address, sym_store, new_constraint)
        else:
            if ext_func_name.startswith(('malloc', 'calloc', 'realloc')):
                ext_handler.ext_alloc_mem_call(store, rip, ext_name, block.block_id)
                new_constraint = cfg_helper.insert_new_constraints(store, rip, block.block_id, ext_name, pre_constraint, constraint)
            elif ext_func_name.startswith(('free')):
                succeed = ext_handler.ext_free_mem_call(store, rip, block.block_id)
                if not succeed: 
                    # self._terminate_path_w_pointer_related_errors(block, sym_store, address, inst, False)
                    return
            else:
                mem_preserve_assumption = True if ext_func_address in self.external_mem_preservation else False
                ext_handler.ext_func_call(store, rip, block.block_id, inv_names, mem_preserve_assumption)
                if ext_name in lib.TERMINATION_FUNCTIONS:
                    self.handle_cmc_path_termination(sym_store.store)
                    utils.logger.info('The symbolic execution has been terminated at the path due to the call of the function ' + ext_name + '\n')
                    return
                new_constraint = cfg_helper.insert_new_constraints(store, rip, block.block_id, ext_name, pre_constraint, constraint)
            self.build_ret_branch(block, address, sym_store, new_constraint)
                

    def handle_unresolved_indirect_jumps(self, block, address, inst, constraint, new_address):
        if inst.startswith('jmp '):
            trace_list = []
            if block.address in self.address_jt_entries_map:
                inst_dest, target_addresses = self.address_jt_entries_map[block.address]
                self._reconstruct_new_branches(block, inst_dest, target_addresses)
                res = lib.TRACE_BACK_RET_TYPE.JT_SUCCEED
            else:
                res, _ = self.trace_back_indirect(block, [inst.split(' ', 1)[1].strip()], trace_list)
            if res != lib.TRACE_BACK_RET_TYPE.JT_SUCCEED:
                if constraint is not None:
                    path_reachable = cfg_helper.check_path_reachability(constraint)
                    if path_reachable == False: return
                self.num_of_unresolved_indirects += 1
                self.handle_cmc_path_termination(block.sym_store.store)
                utils.logger.info('Cannot resolve the jump address ' + sym_helper.string_of_address(new_address) + ' of ' + inst + ' at address ' + hex(address))
                utils.logger.info(trace_back.pp_tb_debug_info(res, address, inst))
                # sys.exit('Cannot resolve the jump address ' + sym_helper.string_of_address(new_address) + ' of ' + inst + ' at address ' + hex(address))
            else:
                self.num_of_resolved_indirects += 1
        else:
            if constraint is not None:
                path_reachable = cfg_helper.check_path_reachability(constraint)
                if path_reachable == False: 
                    utils.logger.info('The path is infeasible at the jump address ' + sym_helper.string_of_address(new_address) + ' of ' + inst + ' at address ' + hex(address) + '\n')
                    return
            new_srcs = self._retrieve_sym_srcs(block)
            self.trace_back_sym_addr(block, new_srcs)
            self.num_of_unresolved_indirects += 1
            utils.logger.info('Cannot resolve the jump address ' + sym_helper.string_of_address(new_address) + ' of ' + inst + ' at address ' + hex(address))
            self.handle_cmc_path_termination(block.sym_store.store)
            # sys.exit('Cannot resolve the jump address ' + sym_helper.string_of_address(new_address) + ' of ' + inst + ' at address ' + hex(address))


    def exec_ret_operation(self, block, address, sym_store, constraint, new_address):
        block_id = None
        utils.logger.info(hex(address) + ': the return address is {}'.format(hex(new_address)))
        if new_address in self.address_inst_map:
            if new_address not in self.ret_call_address_map:
                call_target = self._get_prev_inst_target(new_address)
                if call_target:
                    self.ret_call_address_map[new_address] = call_target
            block_id = self.jump_to_block(block, new_address, sym_store, constraint)
        else:
            self.jump_to_dummy(block)
        return block_id


    def build_ret_branch(self, block, address, sym_store, constraint):
        block_id = None
        new_address, alter_address = semantics.ret(sym_store.store, block.inst, block.block_id)
        if new_address != None:
            if sym_helper.sym_is_int_or_bitvecnum(new_address):
                block_id = self.exec_ret_operation(block, address, sym_store, constraint, new_address)
            elif sym_helper.is_term_address(new_address):
                self.jump_to_dummy(block)
                self.handle_cmc_path_termination(sym_store.store)
            # Return address is symbolic
            else:
                if constraint is not None:
                    path_reachable = cfg_helper.check_path_reachability(constraint)
                    if path_reachable == False: return
                else:
                    if alter_address != None:
                        block_id = self.exec_ret_operation(block, address, sym_store, constraint, alter_address)
                        self.num_of_resolved_indirects += 1
                    else:
                        self.num_of_unresolved_indirects += 1
                        self.handle_cmc_path_termination(sym_store.store)
                        utils.logger.info('Cannot resolve the return address of ' + block.inst + ' at address ' + hex(address))
                        sys.exit('Cannot resolve the return address of ' + block.inst + ' at address ' + hex(address))
            return block_id


    def handle_unbounded_jump_table_w_tb(self, trace_list, src_names, boundary, blk):
        trace_list = trace_list[::-1]
        src_name = src_names[0]
        src_len = utils.get_sym_length(src_name)
        rip = blk.sym_store.rip
        src_sym = sym_engine.get_sym(blk.sym_store.store, rip, src_name, blk.block_id, src_len)
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


    def handle_sym_memwrite_addr(self, blk, count, tb_halt_point, func_call_point, trace_list, sym_names):
        if tb_halt_point or func_call_point:
            res = self._handle_sym_addr_w_concretize(blk, trace_list, sym_names)
        elif count >= utils.MAX_TRACEBACK_COUNT:
            res = lib.TRACE_BACK_RET_TYPE.TB_COUNT_EXCEEDS_LIMITATION
        else:
            res = lib.TRACE_BACK_RET_TYPE.TB_BLOCK_DOES_NOT_EXIST
        return res


    def _get_operand_size(self, inst, arg):
        res = utils.MEM_ADDR_SIZE
        inst_elem = Inst_Elem(inst)
        if len(inst_elem.inst_args) == 2:
            operand = inst_elem.inst_args[1]
            res = utils.get_sym_length(operand)
        else:
            res = cfg_helper.get_real_length(self.mem_len_map, arg)
        return res


    # example: mov eax,DWORD PTR [rip+0x205a28]        # <optind@@GLIBC_2.2.5>
    def _sym_src_from_mov_with_ext_env(self, blk, constraint):
        store, rip, inst = blk.sym_store.store, blk.sym_store.rip, blk.inst
        new_constraint = constraint
        if inst.startswith('mov'):
            inst_elem = Inst_Elem(inst)
            inst_args = inst_elem.inst_args
            if inst_args[1].endswith(']'):
                address = sym_engine.get_effective_address(store, rip, inst_args[1])
                if sym_helper.is_bit_vec_num(address):
                    address = address.as_long()
                    sym_name = cfg_helper.get_unified_sym_name(self.address_sym_table, address)
                    if sym_name:
                        if sym_name in self.global_pre_constraint:
                            pre_constraint = self.global_pre_constraint[sym_name] if sym_name in self.global_pre_constraint else None
                            new_constraint = cfg_helper.insert_new_constraints(store, rip, blk.block_id, sym_name, pre_constraint, constraint)
        return new_constraint


    def _handle_sym_addr_w_concretize(self, restart_blk, trace_list, sym_names):
        utils.logger.info('Handle symbolized memory address with concretization')
        sym_vals = []
        sym_lens = []
        new_constraint = restart_blk.constraint
        for blockid_sym_list in trace_list:
            for block_id, sym_arg in blockid_sym_list:
                curr_block = self.block_set[block_id]
                new_constraint = self._sym_src_from_mov_with_ext_env(curr_block, new_constraint)
                sym_store = curr_block.sym_store
                length = self._get_operand_size(curr_block.inst, sym_arg)
                sym_val = cfg_helper.get_inv_arg_val(sym_store.store, sym_store.rip, sym_arg, block_id, length)
                if sym_val not in self.sym_addr_valueset_map:
                    sym_vals.append(sym_val)
                    sym_lens.append(length)
        concrete_res = cfg_helper.concretize_sym_arg(sym_vals, sym_lens, new_constraint)
        utils.logger.debug('The following symbolic values are concretized: ' + str(sym_vals))
        utils.logger.debug(concrete_res)
        cfg_helper.update_sym_addr_valueset_map(self.sym_addr_valueset_map, concrete_res)
        res = self._reconstruct_new_branches_w_valueset(restart_blk, sym_vals, sym_names)
        return res


    def _reconstruct_new_branches_w_valueset(self, block, sym_vals, sym_names):
        sym_store = block.sym_store
        utils.logger.info('Reconstruct new branches with concretized value\n')
        for i in range(utils.REBUILD_BRANCHES_NUM):
            new_sym_store = Sym_Store(sym_store.store, sym_store.rip)
            new_sym_store.store[lib.NEED_TRACE_BACK] = False
            new_sym_store.store[lib.POINTER_RELATED_ERROR] = None
            block_id = self._add_new_block(block, block.address, block.inst, new_sym_store, block.constraint, False)
            for sym_val in sym_vals:
                if sym_val in self.sym_addr_valueset_map:
                    self._substitute_sym_arg(new_sym_store.store, new_sym_store.rip, sym_val, self.sym_addr_valueset_map[sym_val][i], block_id, sym_names)
                else:
                    return lib.TRACE_BACK_RET_TYPE.SYMADDR_SYM_NOT_IN_GLOBAL_VALUTSET
        return lib.TRACE_BACK_RET_TYPE.SYMADDR_SUCCEED


    def _substitute_sym_arg(self, store, rip, sym_arg, sym_new, block_id, sym_names):
        for sym_name in sym_names:
            tmp_name = sym_name
            if utils.imm_start_pat.match(sym_name):
                tmp_name = '[' + sym_name + ']'
            prev_v = sym_engine.get_sym(store, rip, tmp_name, block_id)
            sym_engine.set_sym(store, rip, tmp_name, sym_helper.substitute_sym_val(prev_v, sym_arg, sym_new), block_id)


    def trace_back_sym_addr(self, blk, sym_names):
        utils.logger.info('Trace back for symbolized memory address')
        utils.logger.info(hex(blk.address) + ': ' + blk.inst)
        sym_store = blk.sym_store
        store, rip = sym_store.store, sym_store.rip
        tb_halt_point = False
        func_call_point = False
        count, blockid_sym_list = 0, []
        src_names = None
        blockid_sym_list = self._update_blockid_sym_list(blockid_sym_list, store, rip, sym_names)
        sorted(blockid_sym_list, key=lambda bn_pair: bn_pair[0])
        trace_list = []
        while blockid_sym_list and count < utils.MAX_TRACEBACK_COUNT:
            curr_block_id, curr_sym_name = blockid_sym_list.pop()
            if curr_block_id != -1:
                curr_blk = self.block_set[curr_block_id]
                curr_store, curr_rip, curr_inst = curr_blk.sym_store.store, curr_blk.sym_store.rip, curr_blk.inst
                _, p_sym_store = cfg_helper.get_parent_block_info(self.block_set, curr_blk)
                if p_sym_store is None:
                    return lib.TRACE_BACK_RET_TYPE.TB_PARENT_BLOCK_DOES_NOT_EXIST
                src_names, func_call_point, tb_halt_point, m_len_map = semantics_tb_sym.parse_sym_src(self.address_ext_func_map, self.dll_func_info, self.address_inst_map, p_sym_store.store, curr_rip, curr_inst, [curr_sym_name])
                self.mem_len_map.update(m_len_map)
                utils.logger.info('Block id ' + str(curr_block_id) + ': ' + hex(curr_blk.address) + '  ' + curr_blk.inst)
                utils.logger.info(src_names)
                if func_call_point:
                    # self._update_external_assumptions(curr_store, curr_rip, curr_inst, src_names)
                    trace_list.append(blockid_sym_list)
                    # break
                elif tb_halt_point:
                    trace_list.append(blockid_sym_list)
                    # break
                elif trace_back.reach_traceback_halt_point(blockid_sym_list):
                    tb_halt_point = True
                    # self._update_external_assumptions(curr_store, curr_rip, curr_inst, src_names)
                    # break
                else:
                    blockid_sym_list = self._update_blockid_sym_list(blockid_sym_list, p_sym_store.store, curr_rip, src_names)
            # else:
            #     tb_halt_point = True
            #     break
            count += 1
        return count, tb_halt_point, func_call_point, trace_list, sym_names


    def _update_external_assumptions(self, store, rip, inst, src_names):
        jump_address_str = inst.split(' ', 1)[1].strip()
        new_address = smt_helper.get_jump_address(store, rip, jump_address_str)
        self.external_lib_assumptions[new_address] = src_names
        if new_address not in self.external_mem_preservation:
            for src_name in src_names:
                if utils.imm_start_pat.match(src_name):
                    self.external_mem_preservation.append(new_address)


    def _retrieve_bid_sym_list(self, p_store, rip, src_names):
        res = []
        for sym_name in src_names:
            tmp_name = sym_name
            if utils.imm_start_pat.match(sym_name):
                tmp_name = '[' + sym_name + ']'
            b_id = sym_engine.get_sym_block_id(p_store, rip, tmp_name)
            if b_id:
                if (b_id, sym_name) not in res:
                    res.append((b_id, sym_name))
        return res


    # Add new (block_id, sym_name) pair to blockid_sym_list according to current src_names
    def _update_blockid_sym_list(self, blockid_sym_list, p_store, rip, src_names):
        bid_sym_list = self._retrieve_bid_sym_list(p_store, rip, src_names)
        for b_id, sym_name in bid_sym_list:
            if (b_id, sym_name) not in blockid_sym_list:
                blockid_sym_list = self._add_new_b_id_sym_pair(blockid_sym_list, b_id, sym_name)
        return blockid_sym_list


    def _add_new_b_id_sym_pair(self, blockid_sym_list, b_id, sym_name):
        if isinstance(b_id, int):
            blockid_sym_list.append((b_id, sym_name))
        else:
            sym_name_split = sym_name.split(':')
            blockid_sym_list.append((b_id[0], sym_name_split[0]))
            blockid_sym_list.append((b_id[1], sym_name_split[1]))
        return blockid_sym_list


    def _get_parent_store(self, blk):
        store = None
        if blk.parent_id in self.block_set:
            parent_block = self.block_set[blk.parent_id]
            store = parent_block.sym_store.store
        else:
            if blk.inst.startswith('cmp'):
                store = blk.sym_store.store
        return store
            

    def trace_back_indirect(self, blk, sym_names, trace_list):
        utils.logger.info('Resolve indirect jump address')
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
        return lib.TRACE_BACK_RET_TYPE.JT_UNRESOLVED, sym_names


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
        elif utils.check_jmp_with_jump_instr(inst):
            hit_upperbound, new_sym_store = self.check_block_hit_upperbound(parent_blk, sym_store, constraint, address, inst)
            if not hit_upperbound:
                if new_sym_store:
                    sym_store = Sym_Store(new_sym_store.store, rip)
                else:
                    sym_store = Sym_Store(sym_store.store, rip)
                block_id = self._add_new_block(parent_blk, address, inst, sym_store, constraint)
            else:
                res = new_sym_store
                block_id = res.block_id
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
        self.block_set[block_id] = block
        if update_sym_store and inst and not utils.check_branch_inst_wo_call(inst) and not inst.startswith('cmov'):
            semantics.parse_semantics(sym_store.store, sym_store.rip, inst, block_id)
        if sym_store.store[lib.NEED_TRACE_BACK]:
            self._handle_symbolized_mem_addr_w_traceback(block, address, inst, sym_store, constraint)
        elif sym_store.store[lib.POINTER_RELATED_ERROR]:
            self._terminate_path_w_pointer_related_errors(block, sym_store, address, inst)
        else:
            if parent_blk:
                parent_blk.add_to_children_list(block_id)
            if address in self.address_block_map:
                blk, cnt = self.address_block_map[address]
                self.address_block_map[address] = [block, cnt + 1]
                # if blk.block_id in self.block_set:
                #     del self.block_set[blk.block_id]
            else:
                self.address_block_map[address] = [block, 1]
            self.block_stack.append(block)
        return block_id

        
    def add_new_constraint(self, store, constraint, inst, val, prefix='j'):
        new_constraint = constraint
        pred_expr = smt_helper.parse_predicate(store, inst, val, prefix)
        if pred_expr != None:
            new_constraint = Constraint(constraint, pred_expr)
        return new_constraint


    def _retrieve_sym_srcs(self, block):
        self.mem_len_map = {}
        inst_split = block.inst.strip().split(' ', 1)
        inst_args = utils.parse_inst_args(inst_split)
        sym_store = block.sym_store
        new_srcs, _ = smt_helper.get_bottom_source(inst_args[0], sym_store.store, sym_store.rip, self.mem_len_map)
        return new_srcs


    def _handle_symbolized_mem_addr_w_traceback(self, block, address, inst, sym_store, constraint):
        new_srcs = self._retrieve_sym_srcs(block)
        count, tb_halt_point, func_call_point, trace_list, sym_names = self.trace_back_sym_addr(block, new_srcs)
        res = self.handle_sym_memwrite_addr(block, count, tb_halt_point, func_call_point, trace_list, sym_names)
        if res != lib.TRACE_BACK_RET_TYPE.SYMADDR_SUCCEED:
            if constraint is not None:
                path_reachable = cfg_helper.check_path_reachability(constraint)
                if path_reachable == False: return
            print_info = trace_back.pp_tb_debug_info(res, address, inst)
            utils.logger.info(print_info)
            # Unresolved symbolic memory address
            self.cmc_exec_info[6] += 1
        

    def _update_node_with_bid(self, block_id, sym_name, prev_blk):
        node = None
        if block_id in self.block_set:
            node = Tree(None)
            block = self.block_set[block_id]
            node.data = (block, [sym_name], prev_blk)
        return node


    def _locate_pointer_related_error(self, block, init_sym_store, address, inst, sym_names):
        # store, rip = sym_store.store, sym_store.rip
        utils.logger.info('Trace back for pointer-related error')
        utils.logger.info(hex(address) + ': ' + block.inst)
        tb_halt_point = False
        node_stack = []
        trace_list = []
        src_names = None
        bid_sym_list = self._retrieve_bid_sym_list(init_sym_store.store, init_sym_store.rip, sym_names)
        for curr_block_id, curr_sym_name in bid_sym_list:
            node = self._update_node_with_bid(curr_block_id, curr_sym_name, block)
            if node:
                node_stack.append(node)
        utils.logger.info(sym_names)
        while node_stack:
            node = node_stack.pop()
            block, sym_names, _ = node.data
            # utils.logger.info(sym_names)
            # utils.logger.info(hex(block.address) + ': ' + block.inst)
            sym_store, inst = block.sym_store, block.inst
            _, p_sym_store = cfg_helper.get_parent_block_info(self.block_set, block)
            if p_sym_store is None:
                return
            for sym_name in sym_names:
                src_names, func_call_point, tb_halt_point, concrete_val = semantics_tb_memaddr.parse_sym_src(self.address_ext_func_map, self.address_inst_map, self.address_sym_table, p_sym_store.store, sym_store.rip, inst, [sym_name])
                utils.logger.info(hex(block.address) + ': ' + block.inst)
                utils.logger.info(src_names)
                bid_sym_list = self._retrieve_bid_sym_list(p_sym_store.store, p_sym_store.rip, src_names)
                if func_call_point or tb_halt_point:
                    trace_list.append(node)
                    # tmp_list = bid_sym_list.copy()
                    # tmp_list.append((curr_block_id, src_names[0]))
                    # tmp_list = self._update_blockid_sym_list(tmp_list, p_sym_store.store, p_sym_store.rip, src_names)
                    # trace_list.append(tmp_list)
                    # return
                elif concrete_val:
                    continue
                else:
                    for b_id, src_name in bid_sym_list:
                    # for src_name in src_names:
                    #     tmp_name = src_name
                    #     if utils.imm_start_pat.match(src_name):
                    #         tmp_name = '[' + src_name + ']'
                    #     b_id = sym_engine.get_sym_block_id(p_sym_store.store, p_sym_store.rip, tmp_name)
                        if b_id:
                            if b_id != -1:
                                new_blk = self.block_set[b_id]
                                new_node = Tree(node)
                                new_node.data = (new_blk, [src_name], block)
                                node.children_list.append(new_node)
                                node_stack.append(new_node)
                            else:
                                trace_list.append(node)
                                # tmp_list = bid_sym_list.copy()
                                # tmp_list.append((curr_block_id, src_names[0]))
                                # tmp_list = self._update_blockid_sym_list(tmp_list, p_sym_store.store, p_sym_store.rip, src_names)
                                # trace_list.append(tmp_list)
                                # return
        if func_call_point or tb_halt_point:
            for node in trace_list:
                cfg_helper.print_tree_path_info(init_sym_store, node, self.address_sym_table)
        utils.logger.info('\n\n')


    def _terminate_path_w_pointer_related_errors(self, block, sym_store, address, inst, common=True):
        utils.output_logger.info('Terminate path with pointer-related error at ' + hex(address) + ': ' + inst)
        sym_names = cfg_helper.retrieve_source_for_memaddr(inst, common)
        if sym_names:
            self._locate_pointer_related_error(block, sym_store, address, inst, sym_names)
            # number of paths
            self.cmc_exec_info[0] += 1
            # number of negative paths
            self.cmc_exec_info[2] += 1
            self._update_pointer_related_error_info(sym_store.store)
        else:
            # number of paths
            self.cmc_exec_info[0] += 1
            # number of negative paths
            self.cmc_exec_info[2] += 1
            self._update_pointer_related_error_info(sym_store.store)
        

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
        blk, cnt = self.address_block_map[new_address]
        if cnt > utils.MAX_VISIT_COUNT:
            return True
        elif cnt == 0: return False
        prev_sym_store = blk.sym_store
        new_inst = self.address_inst_map[new_address]
        new_sym_store = Sym_Store(sym_store.store, prev_sym_store.rip)
        semantics.parse_semantics(new_sym_store.store, new_sym_store.rip, new_inst, -1)
        res = new_sym_store.state_ith_eq(prev_sym_store)
        return res


    def _jump_to_next_block(self, block, address, sym_store, constraint):
        new_address = cfg_helper.get_next_address(address, self.address_next_map, self.address_sym_table)
        if new_address != -1:
            self.jump_to_block(block, new_address, sym_store, constraint)


    def check_block_hit_upperbound(self, block, sym_store, constraint, new_address, new_inst):
        _exist, res = self._exist_block(sym_store, constraint, new_address, new_inst)
        if _exist:
            block.add_to_children_list(res.block_id)
            return True, res
        else:
            return False, res


    def _exist_block(self, sym_store, constraint, new_address, new_inst):
        if new_address in self.address_block_map:
            blk, cnt = self.address_block_map[new_address]
            if cnt == 0:
                return False, None
            elif cnt > utils.MAX_VISIT_COUNT:
                utils.logger.info('Instruction ' + new_inst + ' at address ' + hex(new_address) + ' is visited for ' + str(cnt) + ' times\n')
                return True, blk
            prev_sym_store = blk.sym_store
            rip = prev_sym_store.rip
            new_sym_store = Sym_Store(sym_store.store, rip)
            new_sym_store.merge_store(prev_sym_store, self.address_inst_map)
            if new_sym_store.state_equal(prev_sym_store): 
                utils.logger.info('Block exists: ' + new_inst + ' at address ' + hex(new_address) + ' is visited for ' + str(cnt) + ' times\n')
                return True, blk
            else:
                # self.address_block_map[new_address][0] = cnt + 1
                return False, new_sym_store
        return False, None


    def _update_pointer_related_error_info(self, store):
        if store[lib.POINTER_RELATED_ERROR] == lib.MEMORY_RELATED_ERROR_TYPE.NULL_POINTER_DEREFERENCE:
            self.cmc_exec_info[3] += 1
        elif store[lib.POINTER_RELATED_ERROR] == lib.MEMORY_RELATED_ERROR_TYPE.USE_AFTER_FREE:
            self.cmc_exec_info[4] += 1
        elif store[lib.POINTER_RELATED_ERROR] == lib.MEMORY_RELATED_ERROR_TYPE.BUFFER_OVERFLOW:
            self.cmc_exec_info[5] += 1


    def handle_cmc_path_termination(self, store):
        # NUM_OF_PATHS
        self.cmc_exec_info[0] += 1
        if store[lib.POINTER_RELATED_ERROR]:
            # NUM_OF_NEGATIVES
            self.cmc_exec_info[2] += 1
            self._update_pointer_related_error_info(store)
            utils.logger.info('The symbolic execution has been terminated at the path with pointer-related error\n')
        else:
            # NUM_OF_POSITIVES
            self.cmc_exec_info[1] += 1
            # Sound cases
            self.cmc_exec_info[7] += 1
            utils.logger.info('The symbolic execution has been terminated at the path\n')


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

