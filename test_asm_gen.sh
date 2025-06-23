#!/bin/sh
set -e
set -f # disable globbing.

LD="${LD:-lld}"
CFLAGS="${CFLAGS} -fpie -fno-omit-frame-pointer -gsplit-dwarf -march=native -fuse-ld=${LD} -Wno-unused-function"
LDFLAGS="${LDFLAGS} -Wl,--gc-sections -flto"

CC="${CC:-clang}"
WARNINGS="$(tr -s '\n' ' ' < compile_flags.txt)"

# shellcheck disable=SC2086
$CC $WARNINGS -g3 test_asm_gen.c -o test_asm_gen.bin $CFLAGS $LDFLAGS
./test_asm_gen.bin
