# binary-cmc: Disassembly Soundness Validation

binary-cmc is a tool that automatically validates the soundness of a disassembly process.

binary-cmc structure:

    benchmark

    micro-benchmark

    src

    LICENSE

    README.md


Prerequisites:

    python3 (>= 3.7.1)

    java (>=11.0.2)

    objdump (>= 2.30)


Note:

    -- The compiled binary files for Coreutils are located at binary-cmc/benchmark/coreutils-build

    -- The test cases used in Section 5.2 is stored in binary-cmc/litmus-test


Apply binary-cmc to construct a CFG on a specific file disasembled by a disassembler and get the information regarding # of instructions and unreachable instructions ...

    $ python -m src.main -e benchmark/coreutils-build -l benchmark/coreutils-radare2 -t radare2 -f basename



Apply binary-cmc to validate the soundness and report all the incorrectly disassembled instructions after the CFG is constructed

    $ python -m src.main -e benchmark/coreutils-build -l benchmark/coreutils-radare2 -t radare2 -f basename -s



Use binary-cmc to build up the CFG for all the files under a directory

    $ python -m src.main -e benchmark/coreutils-build -l benchmark/coreutils-radare2 -t radare2 -b



Use binary-cmc to validate the soundness of all the files under a directory after the CFGs are constructed

    $ python -m src.main -e benchmark/coreutils-build -l benchmark/coreutils-radare2 -t radare2 -b -s


