#include "amd64.h"
#include "asm.h"
#include "elf.h"
#if 0
#include "type_check.h"
#endif

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

  AstParser parser = {.lexer = lexer, .errors = &errors};
  ast_emit(&parser, allocator);

  if (cli_opts.verbose) {
    printf("\n------------ AST ------------\n");
    ast_print_nodes(parser.nodes, (MetadataDyn){0});
  }
  ast_constant_fold(parser.nodes, allocator);
  if (cli_opts.verbose) {
    printf("\n------------ AST constant folded ------------\n");
    ast_print_nodes(parser.nodes, (MetadataDyn){0});
  }

  ast_trim_tombstoned(&parser.nodes);

  FnDefinitionDyn fn_defs = ast_generate_fn_defs(&parser, allocator);
  if (cli_opts.verbose) {
    printf("\n------------ AST with metadata ------------\n");
    ast_print_fn_defs(fn_defs, parser.nodes);
  }

#if 0
  TypeChecker type_checker = types_make_type_checker(allocator);
  (void)type_checker; // TODO
#endif
  if (errors.len) {
    goto err;
  }

  PgString base_path = pg_path_base_name(file_path);
  PgString exe_path = pg_string_concat(base_path, PG_S(".bin"), allocator);
  AsmEmitter *asm_emitter =
      amd64_make_asm_emitter(parser.nodes, exe_path, allocator);
  asm_emit(asm_emitter, fn_defs, cli_opts.verbose, allocator);

  if (cli_opts.verbose) {
    printf("\n------------ ASM %.*s ------------\n",
           (i32)asm_emitter->program.file_path.len,
           asm_emitter->program.file_path.data);
    asm_emitter->print_program(*asm_emitter);
  }

  PgError err_write = elf_write_exe(asm_emitter, allocator);
  if (err_write) {
    fprintf(stderr, "failed to write to file %.*s: %u\n",
            (i32)asm_emitter->program.file_path.len,
            asm_emitter->program.file_path.data, err_write);
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
    origin_print(err.origin);
    printf(" Error: ");
    error_print(err);
  }
  return 1;
}
