#include "elf.h"

int main() {
  u64 vm_start = 1 << 22;
  u64 rodata_offset = 0x2000;

  Amd64Constant rodata[] = {
      {
          .name = PG_S("hello_world"),
          .kind = AMD64_CONSTANT_KIND_BYTES,
          .bytes = PG_S("Hello, world!"),
          // TODO: Should it be backpatched?
          .address_absolute = vm_start + rodata_offset + 0x00,
      },
  };
  const Amd64Instruction ops[] = {
      {
          .kind = AMD64_INSTRUCTION_KIND_MOV,
          .dst = {.kind = AMD64_OPERAND_KIND_REGISTER, .reg = amd64_rax},
          .src =
              {
                  .kind = AMD64_OPERAND_KIND_IMMEDIATE,
                  .immediate = 1 /* write(2) */,
              },
      },
      {
          .kind = AMD64_INSTRUCTION_KIND_MOV,
          .dst = {.kind = AMD64_OPERAND_KIND_REGISTER, .reg = amd64_rdi},
          .src =
              {
                  .kind = AMD64_OPERAND_KIND_IMMEDIATE,
                  .immediate = 1 /* stdout */,
              },
      },
      {
          .kind = AMD64_INSTRUCTION_KIND_LEA,
          .dst = {.kind = AMD64_OPERAND_KIND_REGISTER, .reg = amd64_rsi},
          .src =
              {
                  .kind = AMD64_OPERAND_KIND_EFFECTIVE_ADDRESS,
                  .effective_address =
                      {
                          .displacement = (u32)rodata[0].address_absolute,
                      },
              },
      },
      {
          .kind = AMD64_INSTRUCTION_KIND_MOV,
          .dst = {.kind = AMD64_OPERAND_KIND_REGISTER, .reg = amd64_rdx},
          .src =
              {
                  .kind = AMD64_OPERAND_KIND_IMMEDIATE,
                  .immediate = 13,
              },
      },
      {
          .kind = AMD64_INSTRUCTION_KIND_SYSCALL,
      },
      {
          .kind = AMD64_INSTRUCTION_KIND_MOV,
          .dst = {.kind = AMD64_OPERAND_KIND_REGISTER, .reg = amd64_rax},
          .src =
              {
                  .kind = AMD64_OPERAND_KIND_IMMEDIATE,
                  .immediate = 60 /* exit */,
              },
      },
      {
          .kind = AMD64_INSTRUCTION_KIND_SYSCALL,
      },
  };
  Amd64Section section_start = {
      .name = PG_S("_start"),
      .flags = AMD64_SECTION_FLAG_GLOBAL,
      .instructions = {.data = (Amd64Instruction *)ops,
                       .len = PG_STATIC_ARRAY_LEN(ops)},
  };

  Amd64Program program = {
      .file_name = PG_S("asm.bin"),
      .vm_start = vm_start,
      .text =
          {
              .data = &section_start,
              .len = 1,
          },
      .rodata =
          {
              .data = rodata,
              .len = PG_STATIC_ARRAY_LEN(rodata),
          },
  };

  PgArena arena = pg_arena_make_from_virtual_mem(128 * PG_KiB);
  PgArenaAllocator arena_allocator = pg_make_arena_allocator(&arena);
  PgAllocator *allocator = pg_arena_allocator_as_allocator(&arena_allocator);

  PgError err_write = elf_write_exe(program, allocator);
  if (err_write) {
    fprintf(stderr, "failed to write to file %.*s: %u\n",
            (i32)program.file_name.len, program.file_name.data, err_write);
    return 1;
  }
}
