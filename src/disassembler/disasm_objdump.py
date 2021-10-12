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
import os
from types import new_class
from ..common import utils
from ..common.inst_element import Inst_Elem
from . import helper
from .disasm import Disasm


label_address_pattern = re.compile('^[0-9a-f]+ <[A-Za-z_@.0-9]+>:')
address_inst_pattern = re.compile('^[0-9a-f]+:[0-9a-f\t ]+')


class Disasm_Objdump(Disasm):
    def __init__(self, disasm_path):
        self.disasm_path = disasm_path
        self.address_inst_map = {}
        self.address_next_map = {}
        self.address_label_map = {}
        self.address_func_map = {}
        self.address_ext_func_map = {}
        self.func_call_order = ['_start']
        self.funct_call_map = {}
        self.valid_address_no = 0
        self.read_asm_info()


    def get_address_inst_map(self):
        return self.address_inst_map


    def read_asm_info(self):
        with open(self.disasm_path, 'r') as f:
            lines = f.readlines()
            for line in lines:
                line = line.strip()
                if label_address_pattern.search(line):
                    address, label = self._parse_address_label(line)
                    if label not in utils.INVALID_SECTION_LABELS:
                        # new_label = label.split('@', 1)[0].strip()
                        new_label = label.strip()
                        self.address_label_map[address] = [new_label]
                        if '@' not in label:
                            label = label.strip()
                            self.address_func_map[address] = label
                        else:
                            self.address_ext_func_map[address] = label
                elif address_inst_pattern.search(line):
                    address, inst, bin_len = self._parse_line(line)
                    if inst:
                        if inst.startswith('addr32 '):
                            inst = inst.split('addr32', 1)[1].strip()
                        inst = self._format_inst(address, inst)
                        self._construct_func_call_map(label, inst)
                        self.address_inst_map[address] = inst
                        self.valid_address_no += 1
        inst_addresses = sorted(list(self.address_inst_map.keys()))
        inst_num = len(inst_addresses)
        self._replace_addr_w_label()
        self.create_func_call_order()
        for idx, address in enumerate(inst_addresses):
            n_idx = idx + 1
            if n_idx < inst_num:
                rip = inst_addresses[n_idx]
            else:
                rip = address + bin_len
            self.address_next_map[address] = rip


    def _construct_func_call_map(self, label, inst):
        if inst.startswith('call '):
            address_str = inst.split(' ', 1)[1].strip()
            if utils.imm_start_pat.match(address_str):
                address = int(address_str, 16)
                if label in self.funct_call_map:
                    self.funct_call_map[label].append(address)
                else:
                    self.funct_call_map[label] = [address]


    def _replace_addr_w_label(self):
        for label in self.funct_call_map:
            address_list = self.funct_call_map[label]
            for idx, address in enumerate(address_list):
                if address in self.address_func_map:
                    self.funct_call_map[label][idx] = self.address_func_map[address]
                else:
                    self.funct_call_map[label][idx] = None


    def create_func_call_order(self):
        func_stack = ['main']
        while func_stack:
            func_name = func_stack.pop()
            if func_name in self.funct_call_map:
                idx = len(self.func_call_order)
                called_func_list = self.funct_call_map[func_name]
                for called_func in called_func_list:
                    if called_func:
                        if called_func in self.func_call_order:
                            curr_idx = self.func_call_order.index(called_func)
                            if curr_idx < idx:
                                idx = curr_idx
                        elif called_func != func_name:
                            func_stack.append(called_func)
                if func_name not in self.func_call_order:
                    self.func_call_order.insert(idx, func_name)
            elif func_name not in self.func_call_order:
                self.func_call_order.append(func_name)



    def _parse_line(self, line):
        address, inst = None, None
        line_split = line.split('\t', 2)
        bin_len = 0
        if len(line_split) == 3:
            address_str = line_split[0].split(':')[0].strip()
            address = int(address_str, 16)
            bin_len = len(line_split[1].strip().split(' '))
            inst = line_split[2].split('#')[0].split('<')[0].strip()
        return address, inst, bin_len


    def _parse_address_label(self, line):
        line_split = line.strip().split(' ', 1)
        address = int(line_split[0].strip(), 16)
        label = line_split[1].split('<')[1].split('>')[0].strip()
        return address, label


    def _format_inst(self, address, inst):
        inst_elem = Inst_Elem(inst)
        return inst_elem.normalize(address, self._format_arg)


    def _format_arg(self, address, inst_name, arg):
        res = arg.lower()
        res = helper.convert_to_hex_rep(res)
        res = helper.norm_objdump_arg(inst_name, res)
        if utils.check_jmp_with_address(inst_name):
            if utils.imm_pat_wo_prefix.match(res):
                res = '0x' + res
        return res



