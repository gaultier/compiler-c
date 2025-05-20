// clang -masm=intel -c test.s
// llvm-objdump -M intel -d ./test.o 

.globl _start
_start:
cmp 2, 1
mov rax, 0
cmp rax, 0
je .die

.exit:
mov rax, 60
mov rdi, 0
syscall

.die:
mov rax, 60
mov rdi, 1
syscall
