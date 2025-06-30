// clang -masm=intel -c test.s
// llvm-objdump -M intel -d ./test.o 

// .data
// msg: 
//  .ascii "Hello world!"
// len = . -msg

.text

.globl _start
_start:

mov rdi, 0
call __builtin_amd64_linux_println_u64

mov rdi, 123456789
call __builtin_amd64_linux_println_u64


call __builtin_exit



__builtin_amd64_linux_println_u64:
	push rbp
	mov rbp, rsp
	sub rsp, 24

	// r9: n
	mov r9, rdi
	// rsi: ptr
	lea rsi, [rsp+23]
	// r10: ptr_len
	mov r10, 0 

	mov byte ptr [rsi], '\n'
	inc r10

.loop:
	// n /= 10
	mov rax, r9
	mov r8, 10
  // Reset rem, otherwise we could get fpe.
	xor rdx, rdx
	div r8
	mov r9, rax
	// ptr -= 1
	dec rsi
	// *ptr = '0' + (n %10)
	mov [rsi], dl
	add byte ptr [rsi], '0'

	// ptr_len += 1
	inc r10

	cmp r9, 0
	jnz .loop

	mov rax, 1
	mov rdi, 1
	// rsi already in place.
	mov rdx, r10
	syscall
	xor rax, rax

	add rsp, 24
	pop rbp
	ret

__builtin_exit:
mov rax, 60
mov rdi, 0
syscall

