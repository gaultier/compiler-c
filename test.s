// clang -masm=intel -c test.s
// llvm-objdump -M intel -d ./test.o 

.globl _start
_start:
mov rbp, rsp
sub rbp, 64

cmp qword ptr [rbp-8], 0

mov rcx, 9
mov r11, 10

mov rax, 1
mov rdi, 1
mov r15, 478560413032
mov qword ptr [rbp-8], r15
mov rdx, 5
syscall

mov rax, 60
mov rdi, r11
syscall
