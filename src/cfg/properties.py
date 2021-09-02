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
from ..symbolic import sym_helper
from ..symbolic import sym_engine
from . import cfg_helper


def check_called_saved_regs_convention(sym_store, new_address):
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


def check_changed_arg_val_position(block_set, block, sym_store, start_address, arg, length):
    func_list = []
    blk = block
    store = sym_store.store
    parent_no = block.parent_no
    while parent_no:
        parent_blk = block_set[parent_no]
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


def compare_arg_val_w_original(block_set, block, sym_store, start_address, new_address):
    if len(sym_store.store[lib.TO_BE_VERIFIED_ARGS]) > 0:
        res = True
        for arg in sym_store.store[lib.TO_BE_VERIFIED_ARGS]:
            prev_val, length, tmp_res = sym_store.store[lib.TO_BE_VERIFIED_ARGS][arg]
            new_val = sym_engine.get_sym(sym_store.store, new_address, arg, length)
            if not sym_helper.strict_bitvec_equal(prev_val, new_val):
                if sym_helper.is_bv_sym_var(new_val):
                    res = False
                    func_list = check_changed_arg_val_position(block_set, block, sym_store, start_address, arg, length)
                    if func_list:
                        sym_store.store[lib.TO_BE_VERIFIED_ARGS][arg][2] = False & tmp_res if tmp_res is not None else True
                        utils.output_logger.info('Function ' + sym_store.store[lib.VERIFIED_FUNC_INFO][1] + ' might preserve the value at ' + arg + ' if ' + str(func_list) + ' preserve ' + arg + ' at specific path.\n')
                    else:
                        sym_store.store[lib.TO_BE_VERIFIED_ARGS][arg][2] = False
                        utils.output_logger.info('Function ' + sym_store.store[lib.VERIFIED_FUNC_INFO][1] + ' does NOT preserve the value at ' + arg + ' at specific path.\n')
                else:
                    res = False
                    sym_store.store[lib.TO_BE_VERIFIED_ARGS][arg][2] = False
                    utils.output_logger.info('Function ' + sym_store.store[lib.VERIFIED_FUNC_INFO][1] + ' does NOT preserve the value at ' + arg + ' at specific path.\n')
        args = list(sym_store.store[lib.TO_BE_VERIFIED_ARGS].keys())
        if res:
            utils.output_logger.info('Function ' + sym_store.store[lib.VERIFIED_FUNC_INFO][1] + ' DOES preserve the value at ' + str(args) + ' at specific path.\n')

