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

from enum import Enum

FLAG_CONDITIONS = {
    'a': 'CF==0 and ZF==0',
    'ae': 'CF==0',
    'b': 'CF==1',
    'be': 'CF==1 or ZF==1',
    'c': 'CF==1',
    'e': 'ZF==1',
    'g': 'ZF==0 and SF==OF',
    'ge': 'SF==OF',
    'l': 'SF<>OF',
    'le': 'ZF==1 or SF<>OF',
    'na': 'CF==1 or ZF==1',
    'nae': 'CF==1',
    'nb': 'CF==0',
    'nbe': 'CF==0 and ZF==0',
    'nc': 'CF==0',
    'ne': 'ZF==0',
    'ng': 'ZF==1 or SF<>OF',
    'nge': 'SF<>OF',
    'nl': 'SF==OF',
    'nle': 'ZF==0 and SF==OF',
    'no': 'OF==0',
    'np': 'PF==0',
    'ns': 'SF==0',
    'nz': 'ZF==0',
    'o': 'OF==1',
    'p': 'PF==1',
    'pe': 'PF==1',
    'po': 'PF==0',
    's': 'SF==1',
    'z': 'ZF==1',
}

REG_INFO_DICT = {
    'ah': ('rax', 8, 8),
    'bh': ('rbx', 8, 8),
    'ch': ('rcx', 8, 8),
    'dh': ('rdx', 8, 8),
    'eax': ('rax', 0, 32),
    'ax': ('rax', 0, 16),
    'al': ('rax', 0, 8),
    'ebx': ('rbx', 0, 32),
    'bx': ('rbx', 0, 16),
    'bl': ('rbx', 0, 8),
    'ecx': ('rcx', 0, 32),
    'cx': ('rcx', 0, 16),
    'cl': ('rcx', 0, 8),
    'edx': ('rdx', 0, 32),
    'dx': ('rdx', 0, 16),
    'dl': ('rdx', 0, 8),
    'esi': ('rsi', 0, 32),
    'si': ('rsi', 0, 16),
    'sil': ('rsi', 0, 8),
    'edi': ('rdi', 0, 32),
    'di': ('rdi', 0, 16),
    'dil': ('rdi', 0, 8),
    'ebp': ('rbp', 0, 32),
    'bp': ('rbp', 0, 16),
    'bpl': ('rbp', 0, 8),
    'esp': ('rsp', 0, 32),
    'sp': ('rsp', 0, 16),
    'spl': ('rsp', 0, 8),
    'r8d': ('r8', 0, 32),
    'r8w': ('r8', 0, 16),
    'r8b': ('r8', 0, 8),
    'r9d': ('r9', 0, 32),
    'r9w': ('r9', 0, 16),
    'r9b': ('r9', 0, 8),
    'r10d': ('r10', 0, 32),
    'r10w': ('r10', 0, 16),
    'r10b': ('r10', 0, 8),
    'r11d': ('r11', 0, 32),
    'r11w': ('r11', 0, 16),
    'r11b': ('r11', 0, 8),
    'r12d': ('r12', 0, 32),
    'r12w': ('r12', 0, 16),
    'r12b': ('r12', 0, 8),
    'r13d': ('r13', 0, 32),
    'r13w': ('r13', 0, 16),
    'r13b': ('r13', 0, 8),
    'r14d': ('r14', 0, 32),
    'r14w': ('r14', 0, 16),
    'r14b': ('r14', 0, 8),
    'r15d': ('r15', 0, 32),
    'r15w': ('r15', 0, 16),
    'r15b': ('r15', 0, 8)
}


AUX_REG_INFO = {
    8: ('al', 'ah', 'ax'),
    16: ('ax', 'dx', 'dx:ax'),
    32: ('eax', 'edx', 'edx:eax'),
    64: ('rax', 'rdx', 'rdx:rax')
}

COLOR_ERROR_MAPPING = {
    'red': 'null pointer dereference',
    'purple': 'use after free',
    'grey': 'buffer overflow',
    'yellow': 'unresolved symbolic memory address',
    'green': 'sound'
}

REG64_NAME_LIST = ['rax', 'rbx', 'rcx', 'rdx', 'rsi', 'rdi',
                   'r8', 'r9', 'r10', 'r11', 'r12', 'r13', 'r14', 'r15', 'rsp', 'rbp']

REG64_NAMES = {'rax', 'rbx', 'rcx', 'rdx', 'rsp', 'rbp', 'rsi', 'rdi',
               'r8', 'r9', 'r10', 'r11', 'r12', 'r13', 'r14', 'r15'}

REG_NAMES = REG64_NAMES | set(REG_INFO_DICT.keys())

CONDITIONAL_JMP_INST = set(map(lambda x: 'j' + x, FLAG_CONDITIONS.keys()))

RFlags = ['CF', 'ZF', 'OF', 'SF']

SEG_REGS = {'ss', 'cs', 'ds', 'es', 'fs', 'gs'}

CALLEE_NOT_SAVED_REGS = ['rax', 'rcx', 'rdx', 'rsi', 'rdi', 'r8', 'r9', 'r10', 'r11']

JMP_INST = CONDITIONAL_JMP_INST | {'jmp', 'call', 'ret'}

JMP_INST_WITHOUT_CALL = CONDITIONAL_JMP_INST | {'jmp', 'ret'}

JMP_INST_WITH_ADDRESS = CONDITIONAL_JMP_INST | {'jmp', 'call'}

DEFAULT_REG_LEN = 64
C_INT_LEN = 32

REG = 'register'
MEM = 'memory'
FLAGS = 'flags'
FS = 'fs'
CS = 'cs'
GS = 'gs'
AUX_MEM = 'aux_memory'
STDIN = 'stdin'
STDOUT = 'stdout'
STDIN_ADDRESS = 'stdin_address'
STDIN_HANDLER = 'stdin_handler'
STDOUT_ADDRESS = 'stdout_address'
STDOUT_HANDLER = 'stdout_handler'
NEED_TRACE_BACK = 'need_trace_back'
POINTER_RELATED_ERROR = 'pointer_related_error'
VERIFIED_FUNC_INFO = 'verified_func_info'
TO_BE_VERIFIED_ARGS = 'to_be_verified_args'
MEM_CONTENT_POLLUTED = 'mem_content_polluted'
HEAP_ADDR = 'heap_addr'

STATE_NAMES = {REG, MEM, FLAGS, FS, CS, GS, AUX_MEM, STDOUT}
RECORD_STATE_NAMES = [REG, MEM]

TERMINATION_FUNCTIONS = {
    "__stack_chk_fail",
    "__overflow",
    "err",
    "error",
    "error_at_line",
    "errx",
    "exit",
    "_exit",
    "abort",
    "raise",
    "__assert_fail",
    "g_assertion_message_expr",
    "g_assertion_message",
    "g_abort",
    "obstack_alloc_failed_handler",
    "pthread_exit"
}


GENERAL_INSTRUCTIONS = {
    'mov', 'lea', 'push', 'pop', 'add', 'sub', 'xor',
    'and', 'or', 'sar', 'shr', 'sal', 'shl', 'xchg',
    'neg', 'not', 'test', 'cmp', 'imul', 'mul', 'idiv', 'div',
    'cmpxchg', 'movzx', 'movsx', 'movsxd', 'leave', 'inc', 'dec', 'adc', 'sbb',
    'cbw', 'cwde', 'cdqe', 'cwd', 'cdq', 'cqo', 'ror', 'rol', 'nop', 'hlt'
}


INSTS_AFF_FLAGS_WO_CMP_TEST = {
    'add', 'sub', 'xor', 'and', 'or', 'sar', 'shr', 'sal', 'shl',
    'neg', 'not', 'imul', 'mul', 'inc', 'dec', 'adc', 'sbb', 'ror', 'rol'
}

CONDITIONAL_MOV_INST = set(map(lambda x: 'cmov' + x, FLAG_CONDITIONS.keys()))

CONDITIONAL_SET_INST = set(map(lambda x: 'set' + x, FLAG_CONDITIONS.keys()))

INSTRUCTIONS = GENERAL_INSTRUCTIONS | JMP_INST | CONDITIONAL_MOV_INST | CONDITIONAL_SET_INST 


class MEM_DATA_SECT_STATUS(Enum):
    RAW = 0
    POLLUTED = 1
    RESTORED = 2


class MEMORY_RELATED_ERROR_TYPE(Enum):
    NULL_POINTER_DEREFERENCE = 1
    USE_AFTER_FREE = 2
    FREE_AFTER_FREE = 3
    BUFFER_OVERFLOW = 4


class TRACE_BACK_TYPE(Enum):
    INDIRECT = 1
    SYMBOLIC = 2


class TRACE_BACK_RET_TYPE(Enum):
    JT_UNRESOLVED = 0
    JT_SUCCEED = 1
    JT_NO_UPPERBOUND = 2
    JT_NOT_ASSIGN_INST = 3
    JT_NO_DISTINCT_ENTRIES = 4
    JT_NO_TARGET_ADDRESSES = 5
    SYMADDR_SUCCEED = 6
    SYMADDR_NO_FUNC_INVARIANTS = 7
    SYMADDR_W_FUNC_INDOUBT = 8
    SYMADDR_UNINITIALIZED_MEM_CONTENT = 9
    SYMADDR_SYM_NOT_IN_GLOBAL_VALUTSET = 10
    TB_PARENT_BLOCK_DOES_NOT_EXIST = 11
    TB_BLOCK_DOES_NOT_EXIST = 12
    TB_EXCEEDS_LIMITATION = 13

class Tree(object):
    def __init__(self, parent=None):
        self.parent = parent
        self.data = None
        self.children_list = []

