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
from .graph import Graph
from .graph_node import Node


class Construct_Graph(object):
    def __init__(self, log_path, address_inst_map, inst_addresses, block_start_addrs):
        self.node_set = {}
        self.graph = Graph()
        self.address_entries_map = {}
        self.call_to_addr_set = set()
        self.address_inst_map = address_inst_map
        self.inst_addresses = inst_addresses
        self.block_start_addrs = block_start_addrs
        self.organize_address_entires(log_path)
        new_content = self.construct_splitted_content(block_start_addrs)
        self.construct_graph(new_content, inst_addresses)


    def construct_nodes(self, start_address, end_address, inst_addresses):
        node = Node(start_address, end_address, inst_addresses)
        self.node_set[start_address] = node
        self.graph.add_vertex(start_address)


    def construct_edges(self, address):
        if address in self.address_entries_map:
            address_entries = self.address_entries_map[address]
            for addr in address_entries:
                node_id = self.search_node_id(addr)
                if node_id:
                    if address != node_id:
                        self.graph.add_edge([node_id, address])


    def search_node_id(self, address):
        node_id = None
        for start_addr, end_addr in zip(self.start_address_list, self.end_address_list):
            if address >= start_addr and address <= end_addr:
                node = self.node_set[start_addr]
                if node.located_in_this_node(address):
                    node_id = start_addr
                break
        return node_id

    def divide_to_block(self, new_content):
        start_address_list = []
        end_address_list = []
        _exists = False
        lines = new_content.split('\n')
        for line in lines:
            if line:
                address_str, _ = line.strip().split(':', 1)
                address = int(address_str, 16)
                if not _exists:
                    start_address_list.append(address)
                    _exists = True
            else:
                if _exists:
                    end_address_list.append(address)
                _exists = False
        return start_address_list, end_address_list


    def construct_graph(self, new_content, inst_addresses):
        self.start_address_list, self.end_address_list = self.divide_to_block(new_content)
        for start_address, end_address in zip(self.start_address_list, self.end_address_list):
            self.construct_nodes(start_address, end_address, inst_addresses)
        for start_address in self.start_address_list:
            self.construct_edges(start_address)


    def print_path(self, path):
        for node_id in path:
            node = self.node_set[node_id]
            node.pp_node(self.address_inst_map)
            print('\n')

    def gen_path(self, start_vertex, end_vertex, prev_node):
        path = [end_vertex]
        curr = end_vertex
        while curr != start_vertex:
            prev = prev_node[curr]
            path.append(prev)
            curr = prev
        path.reverse()
        return path

    def check_reachable(self, start_vertex, end_vertex, start_addr, end_addr):
        visited = {}
        prev_node = {}
        graph_dict = self.graph.graph_dict()
        for vertex in graph_dict:
            visited[vertex] = False
        queue = []
        queue.append(start_vertex)
        visited[start_vertex] = True
        n = queue.pop(0)
        if n == end_vertex:
            if start_addr <= end_addr:
                return True, self.gen_path(start_vertex, end_vertex, prev_node)
        node = self.node_set[n]
        for v in graph_dict[n]:
            if not visited[v]:
                v_entries = self.address_entries_map[v]
                for ve in v_entries:
                    if node.located_in_this_node(ve):
                        if ve >= start_addr:
                            queue.append(v)
                            prev_node[v] = n
                            visited[v] = True
                            break
        while queue:
            n = queue.pop(0)
            if n == end_vertex:
                return True, self.gen_path(start_vertex, end_vertex, prev_node)
            for v in graph_dict[n]:
                if not visited[v]:
                    queue.append(v)
                    prev_node[v] = n
                    visited[v] = True
        return False, None

    def is_reachable(self, start_addr, end_addr):
        start_node_id = self.search_node_id(start_addr)
        end_node_id = self.search_node_id(end_addr)
        if start_node_id is not None and end_node_id is not None:
            if start_node_id == end_node_id:
                return True
            else:
                res, _ = self.check_reachable(start_node_id, end_node_id, start_addr, end_addr)
                if res:
                    return True
        return False


    def find_path(self, start_addr, end_addr):
        start_node_id = self.search_node_id(start_addr)
        end_node_id = self.search_node_id(end_addr)
        if start_node_id is not None and end_node_id is not None:
            if start_node_id == end_node_id:
                node = self.node_set[start_node_id]
                node.pp_node(self.address_inst_map)
            else:
                res, path = self.check_reachable(start_node_id, end_node_id, start_addr, end_addr)
                if res:
                    self.print_path(path)
                else:
                    print('There is no path')


    def not_continuous(self, prev_address):
        if prev_address:
            p_inst = self.address_inst_map[prev_address]
            if utils.check_branch_inst_wo_call(p_inst):
                return True
            elif p_inst.startswith('call'):
                if prev_address in self.call_to_addr_set:
                    return True
        return False

    def _add_to_address_entries_map(self, addr, entry):
        if addr in self.address_entries_map:
            if entry not in self.address_entries_map[addr]:
                self.address_entries_map[addr].append(entry)
        else:
            self.address_entries_map[addr] = [entry]


    def organize_address_entires(self, log_path):
        unreached = False
        with open(log_path, 'r') as f:
            lines = f.readlines()
            for line in lines:
                line = line.strip()
                if line:
                    if unreached:
                        addr, inst = line.split(':', 1)
                        address = int(addr.strip(), 16)
                        inst = inst.strip()
                        if utils.check_jmp_with_address(inst):
                            jump_address_str = inst.split(' ', 1)[1].strip()
                            if utils.imm_pat.match(jump_address_str):
                                jmp_addr = int(jump_address_str, 16)
                                self._add_to_address_entries_map(jmp_addr, address)
                    else:
                        if ': jump address is ' in line or ': the return address is ' in line:
                            infix = ': jump address is ' if ': jump address is ' in line else ': the return address is '
                            line_split = line.split(infix)
                            addr = int(line_split[0].strip(), 16)
                            jmp_addr_str = line_split[1].strip()
                            if utils.imm_pat.match(jmp_addr_str):
                                inst = self.address_inst_map[addr]
                                inst_name = inst.split(' ', 1)[0]
                                jmp_addr = int(jmp_addr_str, 16)
                                if inst_name == 'call':
                                    self._add_to_address_entries_map(jmp_addr, addr)
                                    self.call_to_addr_set.add(addr)
                                else:
                                    self._add_to_address_entries_map(jmp_addr, addr)
                        elif ': jump addresses resolved using jump table ' in line:
                            line_split = line.split(': jump addresses resolved using jump table ')
                            addr = int(line_split[0].strip(), 16)
                            jmp_table_entries = utils.extract_content(line_split[1].strip(), '[')
                            jmp_table_entries = jmp_table_entries.split(',')
                            jump_targets = [utils.imm_str_to_int(x.strip()) for x in jmp_table_entries]
                            for target in jump_targets:
                                self._add_to_address_entries_map(target, addr)
                        elif utils.LOG_UNREACHABLE_INDICATOR in line: 
                            unreached = True


    def construct_splitted_content(self, block_start_addrs):
        new_content = ''
        for address in self.address_inst_map:
            inst = self.address_inst_map[address]
            if address in block_start_addrs:
                new_content += '\n'
            elif self.not_continuous(prev_address):
                prev_inst = self.address_inst_map[prev_address]
                if utils.check_not_single_branch_inst(prev_inst):
                    self._add_to_address_entries_map(address, prev_address)
                new_content += '\n'
            elif address in self.address_entries_map:
                self.address_entries_map[address].append(prev_address)
                new_content += '\n'
            new_content += hex(address) + ': ' + inst + '\n'
            prev_address = address
        return new_content

    def draw(self):
        vertices = self.graph.vertices()
        graph_dict = self.graph.graph_dict()
        res = 'digraph cfg {\n'
        res += '    node [shape=record];\n'
        for vertex in vertices:
            res += self.draw_node(vertex)
            edges = set(graph_dict[vertex])
            for neighbour in edges:
                res += self.draw_edge(vertex, neighbour)
        res += '}'
        with open('cfg.dot', 'w+') as f:
            f.write(res)
        utils.convert_dot_to_png('cfg')

    def draw_node(self, node_id):
        res = '    node_' + hex(node_id) + ' [label=\"'
        res += '<n' + hex(node_id) + '> '
        res += hex(node_id)
        res += '\"];\n'
        return res

    def draw_edge(self, start_node_id, end_node_id):
        res = '    node_' + hex(start_node_id) + ':n' + hex(start_node_id)
        res += ' -> '
        res += 'node_' + hex(end_node_id) + ':n' + hex(end_node_id)
        res += ';\n'
        return res

