#include "amd64.h"
#include "elf.h"
#if 0
#include "type_check.h"
#endif
#include "asm.h"
#include "ir.h"

typedef struct {
  bool verbose;
  bool optimize;
  char *file_path;
} CliOptions;

static void cli_print_help(char *exe) {
  printf("Usage: %s [-O] [-v] <in.unicorn>\n", exe);
}

static CliOptions cli_options_parse(int argc, char *argv[]) {
  PG_ASSERT(argc >= 1);
  char *exe = argv[0];
  if (argc < 2) {
    cli_print_help(exe);
    exit(1);
  }

  CliOptions res = {0};

  i32 c = 0;
  while ((c = getopt(argc, argv, "Ov")) != -1) {
    switch (c) {
    case 'O':
      res.optimize = true;
      break;
    case 'v':
      res.verbose = true;
      break;
    default:
      fprintf(stderr, "Unknown option %c\n", (char)c);
      cli_print_help(exe);
      exit(1);
    }
  }

  if (optind >= argc) {
    fprintf(stderr, "Missing filename <in.unicorn>\n");
    cli_print_help(exe);
    exit(1);
  }

  res.file_path = argv[optind];

  return res;
}

int main(int argc, char *argv[]) {
  CliOptions cli_opts = cli_options_parse(argc, argv);

  PgArena arena = pg_arena_make_from_virtual_mem(16 * PG_MiB);
  PgArenaAllocator arena_allocator = pg_make_arena_allocator(&arena);
  PgAllocator *allocator = pg_arena_allocator_as_allocator(&arena_allocator);

  {
    Amd64Instruction ins = {
        .kind = AMD64_INSTRUCTION_KIND_MOV,
        .lhs =
            (Amd64Operand){
                .kind = AMD64_OPERAND_KIND_REGISTER,
                .size = ASM_OPERAND_SIZE_1,
                .u.reg.value = AMD64_RAX,
            },
        .rhs =
            (Amd64Operand){
                .kind = AMD64_OPERAND_KIND_REGISTER,
                .size = ASM_OPERAND_SIZE_1,
                .u.reg.value = AMD64_R14,
            },
    };
    Pgu8Dyn sb = {0};
    amd64_encode_instruction_mov(&sb, ins, allocator);
  }

  PgString file_path = pg_cstr_to_string(cli_opts.file_path);
  PgStringResult file_read_res =
      pg_file_read_full_from_path(file_path, allocator);
  if (file_read_res.err) {
    fprintf(stderr, "Failed to read file %.*s: %u\n", (i32)file_path.len,
            file_path.data, file_read_res.err);
    return 1;
  }

  ErrorDyn errors = {0};
  Lexer lexer = lex_make_lexer(file_path, file_read_res.res, &errors);
  lex(&lexer, allocator);

  if (cli_opts.verbose) {
    printf("\n------------ Lex tokens ------------\n");
    lex_tokens_print(lexer.tokens);
  }

  AstParser parser = {
      .lexer = lexer,
      .errors = &errors,
  };
  ast_emit(&parser, allocator);

  AstNodeDyn nodes_input = parser.nodes;
  AstNodeDyn nodes_output = {0};
  PG_DYN_ENSURE_CAP(&nodes_output, nodes_input.len, allocator);

  // Constant folding.
  {
    u32 iterations_max = 10;

    for (u32 i = 0; i < iterations_max; i++) {
      if (cli_opts.verbose) {
        printf("\n------------ [%u] Constant fold before ------------\n", i);
        ast_print_nodes(nodes_input);
      }

      nodes_output.len = 0;

      ast_constant_fold(nodes_input, &nodes_output, allocator);
      if (nodes_output.len == nodes_input.len) { // No change.
        break;
      }
      PG_ASSERT(nodes_output.len < nodes_input.len);

      nodes_input = nodes_output;
      if (cli_opts.verbose) {
        printf("\n------------ [%u] Constant fold after ------------\n", i);
        ast_print_nodes(nodes_input);
      }
    }
  }

  IrEmitter ir_emitter = {.errors = &errors, .src = lexer.src};
  FnDefinitionDyn fn_defs =
      ir_emit_from_ast(&ir_emitter, nodes_input, allocator);
  if (cli_opts.verbose) {
    printf("\n------------ IR ------------\n");
    ir_print_fn_defs(fn_defs);
  }

  if (errors.len) {
    goto err;
  }

  PgString stem = pg_path_stem(file_path);
  PgString exe_path = pg_string_concat(stem, PG_S(".bin"), allocator);
  ArchitectureKind arch_target = ARCH_KIND_AMD64; // TODO: CLI opt.
  // TODO: function.
  AsmEmitter asm_emitter = {
      .arch_kind = arch_target,
      .nodes = nodes_input,
      .arch = amd64_arch,
      .program.file_path = exe_path,
      .program.vm_start = 1 << 22,
  };
  asm_emit(&asm_emitter, fn_defs, cli_opts.verbose, allocator);

  if (cli_opts.verbose) {
    printf("\n------------ ASM %.*s ------------\n",
           (i32)asm_emitter.program.file_path.len,
           asm_emitter.program.file_path.data);
    asm_print_program(stdout, asm_emitter);
  }

  PgError err_write = elf_write_exe(&asm_emitter, allocator);
  if (err_write) {
    fprintf(stderr, "failed to write to file %.*s: %u\n",
            (i32)asm_emitter.program.file_path.len,
            asm_emitter.program.file_path.data, err_write);
    return 1;
  }

  if (cli_opts.verbose) {
    printf("arena: use=%lu available=%lu\n", pg_arena_mem_use(arena),
           pg_arena_mem_available(arena));
  }
  return 0;

err:
  qsort(errors.data, errors.len, sizeof(Error),
        err_compare_errors_by_origin_offset);
  for (u64 i = 0; i < errors.len; i++) {
    Error err = PG_SLICE_AT(errors, i);
    origin_print(stderr, err.origin);
    fprintf(stderr, " Error: ");
    error_print(stderr, err);
  }
  return 1;
}
