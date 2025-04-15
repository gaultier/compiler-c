#include "ast.h"
#include "elf.h"
#include "ir.h"
#include "submodules/cstd/lib.c"

int main() {
  PgArena arena = pg_arena_make_from_virtual_mem(128 * PG_KiB);
  PgArenaAllocator arena_allocator = pg_make_arena_allocator(&arena);
  PgAllocator *allocator = pg_arena_allocator_as_allocator(&arena_allocator);

  AstNode *ast_node_lit_3 = pg_arena_new(&arena, AstNode, 1);
  ast_node_lit_3->kind = AST_NODE_KIND_U64;
  ast_node_lit_3->n64 = 3;

  AstNode *ast_node_lit_5 = pg_arena_new(&arena, AstNode, 1);
  ast_node_lit_5->kind = AST_NODE_KIND_U64;
  ast_node_lit_5->n64 = 5;

  AstNode *ast_node_add = pg_arena_new(&arena, AstNode, 1);
  ast_node_add->kind = AST_NODE_KIND_ADD;
  *PG_DYN_PUSH(&ast_node_add->operands, allocator) = *ast_node_lit_3;
  *PG_DYN_PUSH(&ast_node_add->operands, allocator) = *ast_node_lit_5;

  AstNode *ast_node_lit_60 = pg_arena_new(&arena, AstNode, 1);
  ast_node_lit_60->kind = AST_NODE_KIND_U64;
  ast_node_lit_60->n64 = 60;

  AstNode *ast_node_syscall = pg_arena_new(&arena, AstNode, 1);
  ast_node_syscall->kind = AST_NODE_KIND_SYSCALL;
  *PG_DYN_PUSH(&ast_node_syscall->operands, allocator) = *ast_node_lit_60;
  *PG_DYN_PUSH(&ast_node_syscall->operands, allocator) = *ast_node_add;

  IrDyn irs = {0};
  ast_to_ir(*ast_node_syscall, &irs, allocator);
  IrSlice irs_slice = PG_DYN_SLICE(IrSlice, irs);
  irs_print(irs_slice);

  Amd64RegisterAllocator reg_alloc = amd64_make_register_allocator(allocator);

  Amd64InstructionDyn instructions = {0};
  amd64_irs_to_asm(irs_slice, &instructions, &reg_alloc, allocator);

  Pgu8Dyn sb = {0};
  PG_DYN_ENSURE_CAP(&sb, 4 * PG_KiB, allocator);
  amd64_dump_instructions(
      &sb, PG_DYN_SLICE(Amd64InstructionSlice, instructions), allocator);
  PgString s = PG_DYN_SLICE(PgString, sb);
  puts("------------");
  write(1, s.data, s.len);

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
  Amd64Section section_start = {
      .name = PG_S("_start"),
      .flags = AMD64_SECTION_FLAG_GLOBAL,
      .instructions = PG_DYN_SLICE(Amd64InstructionSlice, instructions),
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

  PgError err_write = elf_write_exe(program, allocator);
  if (err_write) {
    fprintf(stderr, "failed to write to file %.*s: %u\n",
            (i32)program.file_name.len, program.file_name.data, err_write);
    return 1;
  }
}
