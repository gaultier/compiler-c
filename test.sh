#!/bin/sh
set -e
set -f # disable globbing.

LD="${LD:-lld}"
CFLAGS="${CFLAGS} -fpie -fno-omit-frame-pointer -gsplit-dwarf -march=native -fuse-ld=${LD} -Wno-unused-function"
LDFLAGS="${LDFLAGS} -Wl,--gc-sections -flto"

CC="${CC:-clang}"
WARNINGS="$(tr -s '\n' ' ' < compile_flags.txt)"

error() {
	printf "ERROR: %s\n" "$1"
	exit 1
}

build() {
case $1 in 
  debug)
    CFLAGS="${CFLAGS} -O0"
    ;;
  debug_sanitizer)
    CFLAGS="${CFLAGS} -O0 -fsanitize=address,undefined -fsanitize-trap=all"
    ;;
  release)
    CFLAGS="${CFLAGS} -O3"
    ;;
  release_sanitizer)
    CFLAGS="${CFLAGS} -O1 -fsanitize=address,undefined -fsanitize-trap=all"
    ;;
	*)
		error "Build mode \"$1\" unsupported!"
		;;
esac

# shellcheck disable=SC2086
$CC $WARNINGS -g3 test.c -o test.bin $CFLAGS $LDFLAGS
}

if [ $# -eq 0 ]; then
	build debug
elif [ $# -eq 1 ]; then
  build "$1"
else
	error "Too many arguments!"
fi

./test.bin
