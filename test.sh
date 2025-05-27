#!/bin/sh
set -e

WITH_VALGRIND="${WITH_VALGRIND:-0}"

./build.sh debug

for f in testdata/*.unicorn; do
  echo "$f"
  bin="$(dirname "$f")/$(basename -s ".unicorn" "$f").bin"

  if [ "$WITH_VALGRIND" -eq 1 ]; then
    valgrind --quiet ./main.bin "$f"
    valgrind --quiet "$bin"
    valgrind --quiet -v ./main.bin "$f"
    valgrind --quiet "$bin"
  else
   ./main.bin "$f"
   ./"$bin"
   ./main.bin -v "$f"
   ./"$bin"
  fi
done

for f in err_testdata/*.unicorn; do
  echo "$f"
  if [ "$WITH_VALGRIND" -eq 1 ]; then
    valgrind --quiet ./main.bin "$f" || true
    valgrind --quiet -v ./main.bin "$f" || true
  else
   ./main.bin "$f" || true
   ./main.bin -v "$f" || true
  fi
done
