// clang -masm=intel -c test.s && ld test.o
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
	// Epilog.
	push rbp
	mov rbp, rsp
	sub rsp, 24

	// r9: n
	mov r9, rdi
	// rsi: ptr
	lea rsi, [rsp+23]
	// r10: ptr_len
	mov r10, 0 

  // *ptr = '\n'
	mov byte ptr [rsi], '\n'

	// ptr_len += 1
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

	// *ptr = n %10
	mov [rsi], dl

	// *ptr += '0'
	add byte ptr [rsi], '0'

	// ptr_len += 1
	inc r10

	// if (0==n) break;
	cmp r9, 0
	jnz .loop

 // Syscall
	mov rax, 1
	mov rdi, 1
	// rsi already in place.
	mov rdx, r10
	syscall
	xor rax, rax

	// Epilog.
	add rsp, 24
	pop rbp
	ret

__builtin_exit:
mov rax, 60
mov rdi, 0
syscall

