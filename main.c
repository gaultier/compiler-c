#include "amd64.h"
#include "asm.h"

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

  PgArena arena = pg_arena_make_from_virtual_mem(4 * PG_KiB);
  PgArenaAllocator arena_allocator = pg_make_arena_allocator(&arena);
  PgAllocator *allocator = pg_arena_allocator_as_allocator(&arena_allocator);

  PgString program_encoded = amd64_encode_program_text(program, allocator);

  for (u64 i = 0; i < program_encoded.len; i++) {
    printf("%#x ", PG_SLICE_AT(program_encoded, i));
  }
}
