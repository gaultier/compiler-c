; clang -masm=intel -c test.s
; llvm-objdump -M intel -d ./test.o 

.globl _start
_start:
add rdx, qword ptr [rbp-0x40000] 
