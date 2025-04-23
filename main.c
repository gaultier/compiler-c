#include "ast.h"
#include "elf.h"
#include "error.h"
#include "ir.h"
#include "lex.h"
#include "submodules/cstd/lib.c"

int main(int argc, char *argv[]) {
  PG_ASSERT(argc >= 1);
  if (2 != argc) {
    fprintf(stderr, "Usage: %s <source file>\n", argv[0]);
    return 1;
  }

  PgArena arena = pg_arena_make_from_virtual_mem(128 * PG_KiB);
  PgArenaAllocator arena_allocator = pg_make_arena_allocator(&arena);
  PgAllocator *allocator = pg_arena_allocator_as_allocator(&arena_allocator);

  PgString file_name = pg_cstr_to_string(argv[1]);
  PgStringResult file_read_res =
      pg_file_read_full_from_path(file_name, allocator);
  if (file_read_res.err) {
    fprintf(stderr, "Failed to read file %.*s: %u\n", (i32)file_name.len,
            file_name.data, file_read_res.err);
    return 1;
  }

  LexTokenDyn tokens = {0};
  ErrorDyn errors = {0};
  lex(file_name, file_read_res.res, &tokens, &errors, allocator);
  if (errors.len) {
    for (u64 i = 0; i < errors.len; i++) {
      Error err = PG_SLICE_AT(errors, i);
      origin_print(err.origin);
      printf(" Error: ");
      error_print(err);
    }
    return 1;
  }
  LexTokenSlice tokens_slice = PG_DYN_SLICE(LexTokenSlice, tokens);
  printf("\n------------ Lex tokens ------------\n");
  lex_tokens_print(tokens_slice);

  AstNode *root = lex_to_ast(tokens_slice, &errors, allocator);
  if (errors.len) {
    for (u64 i = 0; i < errors.len; i++) {
      Error err = PG_SLICE_AT(errors, i);
      origin_print(err.origin);
      printf(" Error: ");
      error_print(err);
    }
    return 1;
  }

  printf("\n------------ AST ------------\n");
  ast_print(*root, 0);

  IrEmitter ir_emitter = {
      .ir_num = 1,
      .label_num = 1,
  };
  ast_to_ir(*root, &ir_emitter, &errors, allocator);
  if (errors.len) {
    for (u64 i = 0; i < errors.len; i++) {
      Error err = PG_SLICE_AT(errors, i);
      origin_print(err.origin);
      printf(" Error: ");
      error_print(err);
    }
    return 1;
  }

  printf("\n------------ IR ------------\n");
  ir_emitter_print_irs(ir_emitter);
  irs_simplify(&ir_emitter.irs, &ir_emitter.var_lifetimes);
  printf("\n------------ IR simplified ------------\n");
  ir_emitter_print_irs(ir_emitter);
  printf("\n------------ IR var lifetimes simplified ------------\n");
  ir_emitter_print_var_lifetimes(ir_emitter);
  IrSlice irs_slice = PG_DYN_SLICE(IrSlice, ir_emitter.irs);

  Amd64RegisterAllocator reg_alloc = amd64_make_register_allocator(allocator);

  Amd64InstructionDyn instructions = {0};
  amd64_emit_prolog(&instructions, allocator);
  amd64_irs_to_asm(irs_slice, &instructions, &reg_alloc, allocator);
  amd64_emit_epilog(&instructions, allocator);

  printf("\n------------ ASM ------------\n");
  amd64_print_instructions(PG_DYN_SLICE(Amd64InstructionSlice, instructions));

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

  PgError err_write = elf_write_exe(&program, allocator);
  if (err_write) {
    fprintf(stderr, "failed to write to file %.*s: %u\n",
            (i32)program.file_name.len, program.file_name.data, err_write);
    return 1;
  }
}
