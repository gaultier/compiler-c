// clang -masm=intel -c test.s
// llvm-objdump -M intel -d ./test.o 

// .data
// msg: 
//  .ascii "Hello world!"
// len = . -msg

.text

.globl _start
_start:
add rax, 4294967295

__builtin_exit:
mov rax, 60
mov rdi, 0
syscall

