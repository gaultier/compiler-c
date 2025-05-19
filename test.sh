#!/bin/sh
set -e

WITH_VALGRIND="${WITH_VALGRIND:-0}"

./build.sh debug
for f in *.unicorn; do
  echo "$f"
  if [ "$WITH_VALGRIND" -eq 1 ]; then
    valgrind --quiet ./main.bin "$f"
    valgrind --quiet ./"$(basename $f)".bin
  else
   ./main.bin "$f"
   ./"$(basename $f)".bin
  fi

done
