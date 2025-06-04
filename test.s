// clang -masm=intel -c test.s
// llvm-objdump -M intel -d ./test.o 

.globl _start
_start:
mov r13b, r14b
mov al, 255
mov ax, 255
mov eax, 255
mov rax, 255

__builtin_println_u64:

__builtin_exit:
mov rax, 60
mov rdi, 0
syscall

