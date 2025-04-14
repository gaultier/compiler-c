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

  PgArena arena = pg_arena_make_from_virtual_mem(4 * PG_KiB);
  PgArenaAllocator arena_allocator = pg_make_arena_allocator(&arena);
  PgAllocator *allocator = pg_arena_allocator_as_allocator(&arena_allocator);

  PgString section_to_string = amd64_dump_section(section_start, allocator);

  printf("%.*s\n", (i32)section_to_string.len, section_to_string.data);
}
