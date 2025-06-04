	.text
	.file	"println_int.c"
	.globl	println_u64                     # -- Begin function println_u64
	.p2align	4, 0x90
	.type	println_u64,@function
println_u64:                            # @println_u64
	.cfi_startproc
# %bb.0:
	pushq	%rbp
	.cfi_def_cfa_offset 16
	.cfi_offset %rbp, -16
	movq	%rsp, %rbp
	.cfi_def_cfa_register %rbp
	subq	$64, %rsp
	movq	%rdi, -8(%rbp)
	leaq	-48(%rbp), %rdi
	xorl	%esi, %esi
	movl	$30, %edx
	callq	memset@PLT
	leaq	-48(%rbp), %rax
	addq	$30, %rax
	movq	%rax, -56(%rbp)
	movq	-56(%rbp), %rax
	movq	%rax, -64(%rbp)
	movq	-56(%rbp), %rax
	movq	%rax, %rcx
	addq	$-1, %rcx
	movq	%rcx, -56(%rbp)
	movb	$10, -1(%rax)
.LBB0_1:                                # =>This Inner Loop Header: Depth=1
	movq	-8(%rbp), %rax
	movl	$10, %ecx
	xorl	%edx, %edx
                                        # kill: def $rdx killed $edx
	divq	%rcx
	addq	$48, %rdx
	movb	%dl, %cl
	movq	-56(%rbp), %rax
	movq	%rax, %rdx
	addq	$-1, %rdx
	movq	%rdx, -56(%rbp)
	movb	%cl, -1(%rax)
	movq	-8(%rbp), %rax
	movl	$10, %ecx
	xorl	%edx, %edx
                                        # kill: def $rdx killed $edx
	divq	%rcx
	movq	%rax, -8(%rbp)
# %bb.2:                                #   in Loop: Header=BB0_1 Depth=1
	cmpq	$0, -8(%rbp)
	jne	.LBB0_1
# %bb.3:
	movq	-56(%rbp), %rdx
	movq	-64(%rbp), %rcx
	movq	-56(%rbp), %rax
	subq	%rax, %rcx
	movl	$1, %edi
	movl	$1, %esi
	movb	$0, %al
	callq	syscall
	addq	$64, %rsp
	popq	%rbp
	.cfi_def_cfa %rsp, 8
	retq
.Lfunc_end0:
	.size	println_u64, .Lfunc_end0-println_u64
	.cfi_endproc
                                        # -- End function
	.globl	main                            # -- Begin function main
	.p2align	4, 0x90
	.type	main,@function
main:                                   # @main
	.cfi_startproc
# %bb.0:
	pushq	%rbp
	.cfi_def_cfa_offset 16
	.cfi_offset %rbp, -16
	movq	%rsp, %rbp
	.cfi_def_cfa_register %rbp
	subq	$32, %rsp
	movq	$0, -8(%rbp)
	movq	-8(%rbp), %rdi
	callq	println_u64
	movq	$1, -16(%rbp)
	movq	-16(%rbp), %rdi
	callq	println_u64
	movq	$124, -24(%rbp)
	movq	-24(%rbp), %rdi
	callq	println_u64
	movq	$999, -32(%rbp)                 # imm = 0x3E7
	movq	-32(%rbp), %rdi
	callq	println_u64
	xorl	%eax, %eax
	addq	$32, %rsp
	popq	%rbp
	.cfi_def_cfa %rsp, 8
	retq
.Lfunc_end1:
	.size	main, .Lfunc_end1-main
	.cfi_endproc
                                        # -- End function
	.ident	"clang version 19.1.7 (Fedora 19.1.7-13.fc42)"
	.section	".note.GNU-stack","",@progbits
	.addrsig
	.addrsig_sym println_u64
	.addrsig_sym syscall
