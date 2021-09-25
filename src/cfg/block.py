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
from ..common import utils

class Block(object):

    cnt = utils.INIT_BLOCK_NO
    
    def __init__(self, parent_id, address, inst, sym_store, constraint):
        self.parent_id = parent_id
        self.address = address
        self.inst = inst
        self.sym_store = sym_store
        self.constraint = constraint
        self.children_blk_list = []
        self.block_id = self.__class__.cnt
        self.__class__.cnt += 1


    def add_to_children_list(self, block_id):
        self.children_blk_list.append(block_id)

    
    def draw(self):
        res = '    block_' + str(self.block_id) + ' [label=\"'
        res += '<b' + str(self.block_id) + '> '
        res += self.inst
        res += '\\l'
        if self.sym_store:
            res += '|' + self.sym_store.draw()
        if self.constraint:
            res += '|' + self.constraint.draw()
        res += '\"];\n'
        return res


    def draw_edge(self):
        res = '    block_' + str(self.block_id) + ':b' + str(self.block_id)
        res += ' -> {'
        for end_block in self.children_blk_list:
            end_block_id = end_block.block_id
            res += 'block_' + str(end_block_id) + ':b' + str(end_block_id)
            res += ' '
        res += '};\n'
        return res

    