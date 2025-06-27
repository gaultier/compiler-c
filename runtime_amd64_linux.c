
typedef unsigned char u8;
typedef unsigned long long int u64;
typedef u64 size_t;

void *memcpy(void *dst, void *src, size_t n) {
  u8 *dst_u8 = dst;
  u8 *src_u8 = src;

  for (u64 i = 0; i < n; i++) {
    *(dst_u8++) = (*src_u8++);
  }
  return dst;
}

void builtin_print_u64(u64 n, u8 *buf, u64 *buf_len,
                       u64 buf_cap) __asm__("builtin.print_u64");

void builtin_print_u64(u64 n, u8 *buf, u64 *buf_len, u64 buf_cap) {
  u8 tmp[24];
  u8 *ptr = tmp + sizeof(tmp);

  do {
    ptr -= 1;
    *ptr = '0' + (n % 10);
    n /= 10;
  } while (n > 0);

  u64 src_len = tmp + sizeof(tmp) - ptr;
  if (*buf_len + src_len > buf_cap) {
    __builtin_trap();
  }

  u8 *dst = buf + *buf_len;
  for (u64 i = 0; i < src_len; i++) {
    *(dst++) = *(ptr++);
  }
  *buf_len += src_len;
}
