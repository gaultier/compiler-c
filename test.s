// clang -masm=intel -c test.s
// llvm-objdump -M intel -d ./test.o 

.globl _start
_start:
cmp rax, 2
