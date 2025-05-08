#!/bin/sh
set -e

./build.sh debug_sanitizer
for f in *.unicorn; do
  echo "$f"
  ./main.bin "$f"
  ./asm.bin
done
