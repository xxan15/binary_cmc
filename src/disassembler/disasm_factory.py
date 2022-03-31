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

from.disasm_idapro import Disasm_IDAPro

class Disasm_Factory(object):
    def __init__(self, disasm_path, exec_path=None, disasm_type='idapro'):
        self.disasm_type = disasm_type
        self.exec_path = exec_path
        self.disasm_path = disasm_path


    def get_disasm(self):
        if self.disasm_type:
            if self.disasm_type == 'idapro':
                return Disasm_IDAPro(self.disasm_path)
        return None

