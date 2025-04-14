#include "elf.h"

int main() {
  const Amd64Instruction ops[] = {
      {
          .kind = AMD64_INSTRUCTION_KIND_MOV,
          .dst = {.kind = AMD64_OPERAND_KIND_REGISTER, .reg = amd64_rax},
          .src =
              {
                  .kind = AMD64_OPERAND_KIND_IMMEDIATE,
                  .immediate = 3,
              },
      },
      {
          .kind = AMD64_INSTRUCTION_KIND_MOV,
          .dst = {.kind = AMD64_OPERAND_KIND_REGISTER, .reg = amd64_rbx},
          .src =
              {
                  .kind = AMD64_OPERAND_KIND_IMMEDIATE,
                  .immediate = 5,
              },
      },
      {
          .kind = AMD64_INSTRUCTION_KIND_ADD,
          .dst = {.kind = AMD64_OPERAND_KIND_REGISTER, .reg = amd64_rax},
          .src =
              {
                  .kind = AMD64_OPERAND_KIND_REGISTER,
                  .reg = amd64_rbx,
              },
      },
      {
          .kind = AMD64_INSTRUCTION_KIND_MOV,
          .dst = {.kind = AMD64_OPERAND_KIND_REGISTER, .reg = amd64_rdi},
          .src =
              {
                  .kind = AMD64_OPERAND_KIND_REGISTER,
                  .reg = amd64_rax,
              },
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
      .text =
          {
              .data = &section_start,
              .len = 1,
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
