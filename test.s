; clang -masm=intel -c test.s

.globl _start
_start:
add rdx, qword ptr [rbp-0x40000] 
