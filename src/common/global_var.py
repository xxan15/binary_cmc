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

from . import utils
from ..binary import Binary_Info
from ..binary import Binary_Content

binary_info = None
binary_content = None

def get_binary_info(exec_path):
    global binary_info
    global binary_content
    binary_info = Binary_Info(exec_path)
    binary_content = Binary_Content(exec_path)
