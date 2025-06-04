// clang -masm=intel -c test.s
// llvm-objdump -M intel -d ./test.o 

.data
msg: 
 .ascii "Hello world!"
len = . -msg

.text

.globl _start
_start:
mov [msg], al
mov al, 255
mov ax, 255
mov eax, 255
mov rax, 255

__builtin_println_u64:

__builtin_exit:
mov rax, 60
mov rdi, 0
syscall

