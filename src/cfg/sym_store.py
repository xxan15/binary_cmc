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
from ..symbolic import sym_helper
from ..common.lib import MEM_DATA_SECT_STATUS

class Sym_Store:
    def __init__(self, store, rip=None):
        self.rip = rip
        if store:
            self.store = store.copy()
            for name in lib.STATE_NAMES:
                self.store[name] = store[name].copy()
        else:
            self.store = {}
            for name in lib.STATE_NAMES:
                if name == lib.FUNC_CALL_STACK:
                    self.store[name] = []
                else:
                    self.store[name] = {}
            self.store[lib.HEAP_ADDR] = utils.MIN_HEAP_ADDR
            self.store[lib.NEED_TRACE_BACK] = False
            self.store[lib.POINTER_RELATED_ERROR] = None
            self.store[lib.MEM_CONTENT_POLLUTED] = utils.INIT_BLOCK_NO


    def pp_val(self, sym):
        res = ''
        if sym_helper.is_bit_vec_num(sym):
            res = hex(sym.as_long()) 
        elif isinstance(sym, list):
            res = self.pp_val(sym[0]) + ', ' + str(sym[1])
        else: res = str(sym)
        return res


    def pp_store(self):
        result = ''
        if self.rip:
            result += 'rip:' + hex(self.rip) + '\n'
        pp_lib_names = [lib.REG, lib.MEM]
        for k in pp_lib_names:
            v = self.store[k]
            res_str = ''
            if k == lib.REG:
                for ki in lib.REG64_NAME_LIST:
                    vi = v[ki]
                    res_str += str(ki) + ': ' + self.pp_val(vi) + ',\n'
            else:
                for ki, vi in v.items():
                    res_str += str(ki) + ': ' + self.pp_val(vi) + ',\n'
            result += k + ':{\n' + res_str + '}\n'
        # result += self.pp_aux_mem()
        # result += lib.STDOUT_ADDRESS + ':' + str(self.store[lib.STDOUT_ADDRESS])
        return result


    def merge_store(self, old, address_inst_map):
        for k in lib.RECORD_STATE_NAMES:
            s = self.store[k]
            s_old = old.store[k]
            for ki, v in s.items():
                v_old = s_old.get(ki, None)
                if v_old is not None:
                    s[ki][0] = sym_helper.merge_sym(v_old[0], v[0], address_inst_map)


    def state_ith_eq(self, old, k=lib.REG):
        s = self.store[k]
        s_old = old.store[k]
        for k in s:
            v = s[k][0]
            v_old = s_old.get(k, None)
            if v_old is not None:
                v_old = v_old[0]
                if not sym_helper.bitvec_eq(v_old, v):
                    return False
        return True


    def state_equal(self, old):
        for k in lib.RECORD_STATE_NAMES:
            res = self.state_ith_eq(old, k)
            if not res:
                return False
        return True


    def draw_store_val(self, val):
        if isinstance(val, str):
            return val
        elif isinstance(val, dict):
            return '\\{' + ', '.join(list(map(lambda k: str(k) + ':' + str(val[k]), val))) + '\\}'
        else:
            return str(val)


    def draw(self):
        res = '\\l'.join(list(map(lambda k: k + '=' + self.draw_store_val(self.store[k]), self.store)))
        res += '\\l'
        return res