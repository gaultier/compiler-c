// clang -masm=intel -c test.s
// llvm-objdump -M intel -d ./test.o 

.globl _start
_start:
mov rbp, rsp
sub rbp, 64


mov qword ptr [rbp-24], 12
mov qword ptr [rbp-32], 45

// mov [rbp-32], [rbp-24]
mov rax, qword ptr [rbp-24]
mov qword ptr [rbp-32], rax

mov rax, 60
mov rdi, qword ptr [rbp-32]
syscall
