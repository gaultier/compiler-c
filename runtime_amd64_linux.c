typedef unsigned char u8;
typedef unsigned long long int u64;
typedef u64 size_t;

static u64 syscall3(u64 sys_num, u64 arg1, u64 arg2, u64 arg3) {
  u64 ret = 0;
  __asm__ __volatile__("syscall"
                       : "=a"(ret)
                       : "a"(sys_num), "D"(arg1), "S"(arg2), "d"(arg3)
                       : "rcx", "r11", "memory");
  return ret;
}

void builtin_println_u64(u64 n) __asm__("builtin.println_u64");

void builtin_println_u64(u64 n) {
  u8 tmp[24];
  u8 *ptr = tmp + sizeof(tmp);

  *(--ptr) = '\n';

  do {
    ptr -= 1;
    *ptr = '0' + (n % 10);
    n /= 10;
  } while (n > 0);

  syscall3(1, 1, (u64)(void *)ptr, (u64)(tmp + sizeof(tmp) - ptr));
}

#if 0
__asm(".intel_syntax\n"
      ".global _start\n"
      "_start:\n"
      "   mov edi, dword ptr [rsp]\n"
      "   lea rsi, [rsp + 8]\n"
      "   lea rdx, [rsi + 8 * rdi + 8]\n"
      "   call main\n"
      "   mov edi, eax\n"
      "   mov eax, 60\n"
      "   syscall\n");
#endif
