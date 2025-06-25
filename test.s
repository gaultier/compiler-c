// clang -masm=intel -c test.s
// llvm-objdump -M intel -d ./test.o 

// .data
// msg: 
//  .ascii "Hello world!"
// len = . -msg

.text

.globl _start
_start:
mov byte ptr [r13], al

__builtin_exit:
mov rax, 60
mov rdi, 0
syscall

