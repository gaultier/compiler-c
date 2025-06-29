CFLAGS := -fpie -fno-omit-frame-pointer -gsplit-dwarf -march=native -fuse-ld=$(LD) -std=c23 -Wall -Wextra -Werror -Wno-gnu-alignof-expression -g3

LDFLAGS := -Wl,--gc-sections -flto

CC := clang

C_FILES := $(wildcard *.c *.h)

SANITIZERS := address,undefined

main_debug.bin: $(C_FILES)
	$(CC) $(CFLAGS) $(LDFLAGS) main.c -o $@

main_debug_sanitizer.bin: $(C_FILES)
	$(CC) $(CFLAGS) $(LDFLAGS) main.c -o $@ -fsanitize=$(SANITIZERS)

main_release.bin: $(C_FILES)
	$(CC) $(CFLAGS) $(LDFLAGS) main.c -o $@ -O2 -flto

main_release_sanitizer.bin: $(C_FILES)
	$(CC) $(CFLAGS) $(LDFLAGS) main.c -o $@ -O2 -flto -fsanitize=$(SANITIZERS)

test_debug.bin: $(C_FILES) main_release.bin
	$(CC) $(CFLAGS) $(LDFLAGS) test.c -o $@ -Wno-unused

test_debug_sanitizer.bin: $(C_FILES) main_release.bin
	$(CC) $(CFLAGS) $(LDFLAGS) test.c -o $@ -fsanitize=$(SANITIZERS) -Wno-unused

test_release.bin: $(C_FILES) main_release.bin
	$(CC) $(CFLAGS) $(LDFLAGS) test.c -o $@ -O2 -flto -Wno-unused

test_release_sanitizer.bin: $(C_FILES) main_release.bin
	$(CC) $(CFLAGS) $(LDFLAGS) test.c -o $@ -O2 -flto -fsanitize=$(SANITIZERS) -Wno-unused

all: main_debug.bin main_debug_sanitizer.bin main_release.bin main_release_sanitizer.bin test_debug.bin test_debug_sanitizer.bin test_release.bin test_release_sanitizer.bin

.PHONY: test
test: test_debug.bin
	./$<


.PHONY: dev
dev: 
	ls *.{c,h} | entr -c make main_debug.bin
