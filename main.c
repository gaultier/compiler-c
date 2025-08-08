#include "amd64.h"
#include "asm.h"
#include "elf.h"
#include "ir.h"

typedef struct {
  PgString file_path;
  PG_PAD(6);
  bool verbose;
  bool optimize;
} CliOptions;

static CliOptions cli_options_parse(int argc, char *argv[],
                                    PgAllocator *allocator) {
  PG_ASSERT(argc >= 1);
  PgString exe = pg_cstr_to_string(argv[0]);

  PgString description =
      PG_S("An experimental compiler targeting x86_64 Linux");
  PgString plain_arguments_description = PG_S("file.unicorn");
  PG_DYN(PgCliOptionDescription) descs = {0};
  PG_DYN_ENSURE_CAP(&descs, 4, allocator);

  *PG_DYN_PUSH_WITHIN_CAPACITY(&descs) = (PgCliOptionDescription){
      .name_short = PG_S("v"),
      .name_long = PG_S("verbose"),
      .description = PG_S("Enable verbose mode"),
  };
#if 0
  *PG_DYN_PUSH_WITHIN_CAPACITY(&descs) = (PgCliOptionDescription){
      .name_short = PG_S("O"),
      .name_long = PG_S("optimize"),
      .description = PG_S("Enable optimizations"),
};
#endif

  PgCliParseResult res_parse = pg_cli_parse(&descs, argc, argv, allocator);
  if (0 != res_parse.err) {
    pg_cli_print_parse_err(res_parse);
    goto die;
  }

  if (res_parse.plain_arguments.len != 1) {
    fprintf(stderr, "Expected one input file, was provided: %" PRIu64 ".",
            res_parse.plain_arguments.len);
    goto die;
  }

  CliOptions res = {0};
  res.file_path = PG_SLICE_AT(res_parse.plain_arguments, 0);

  PG_EACH(opt, res_parse.options) {
    if (pg_string_eq(opt.description.name_long, PG_S("verbose"))) {
      res.verbose = true;
    } else if (pg_string_eq(opt.description.name_long, PG_S("optimize"))) {
      res.optimize = true;
    } else if (pg_string_eq(opt.description.name_long, PG_S("help"))) {
      PgString help = pg_cli_generate_help(
          descs, exe, description, plain_arguments_description, allocator);
      printf("%.*s", (i32)help.len, help.data);

      exit(0);
    }
  }

  return res;

die:
  fprintf(stderr, "\n\n");
  PgString help = pg_cli_generate_help(descs, exe, description,
                                       plain_arguments_description, allocator);
  fprintf(stderr, "%.*s", (i32)help.len, help.data);

  exit(1);
}

int main(int argc, char *argv[]) {
  PgArena arena = pg_arena_make_from_virtual_mem(16 * PG_MiB);
  PgArenaAllocator arena_allocator = pg_make_arena_allocator(&arena);
  PgAllocator *allocator = pg_arena_allocator_as_allocator(&arena_allocator);

  CliOptions cli_opts = cli_options_parse(argc, argv, allocator);

  PgLogLevel log_level =
      cli_opts.verbose ? PG_LOG_LEVEL_DEBUG : PG_LOG_LEVEL_ERROR;
  PgLogger logger =
      pg_log_make_logger_stdout(log_level, PG_LOG_FORMAT_LOGFMT, allocator);

  PgWriter writer_internals = cli_opts.verbose
                                  ? pg_writer_make_from_file_descriptor(
                                        pg_os_stdout(), 4 * PG_KiB, allocator)
                                  : pg_writer_make_noop();

  PG_RESULT(PgString, PgError)
  file_read_res = pg_file_read_full_from_path(cli_opts.file_path, allocator);
  PG_IF_LET_ERR(err, file_read_res) {
    pg_log(&logger, PG_LOG_LEVEL_ERROR, "failed to read file",
           pg_log_c_err("err", err), pg_log_c_s("path", cli_opts.file_path));
    return 1;
  }
  PgString file_content = PG_UNWRAP(file_read_res);
  pg_log(&logger, PG_LOG_LEVEL_INFO, "read input file",
         pg_log_c_s("file_path", cli_opts.file_path),
         pg_log_c_u64("count_bytes", file_content.len));

  PG_DYN(Error) errors = {0};
  Lexer lexer = lex_make_lexer(cli_opts.file_path, file_content, &errors);
  lex(&lexer, allocator);

  pg_log(&logger, PG_LOG_LEVEL_DEBUG, "lex tokens",
         pg_log_c_u64("count", lexer.tokens.len));

  lex_tokens_print(lexer.tokens, &writer_internals, allocator);

  AstParser parser = {
      .lexer = lexer,
      .errors = &errors,
  };
  ast_emit(&parser, allocator);

  PG_DYN(AstNode) nodes_input = parser.nodes;
  PG_DYN(AstNode) nodes_output = {0};
  PG_DYN_ENSURE_CAP(&nodes_output, nodes_input.len, allocator);

  // Constant folding.
  {
    u32 iterations_max = 10;

    for (u32 i = 0; i < iterations_max; i++) {
      pg_log(&logger, PG_LOG_LEVEL_DEBUG, "constant fold before",
             pg_log_c_u64("iteration", i));
      ast_print_nodes(nodes_input, &writer_internals, allocator);

      nodes_output.len = 0;

      ast_constant_fold(nodes_input, &nodes_output, allocator);
      if (nodes_output.len == nodes_input.len) { // No change.
        break;
      }
      PG_ASSERT(nodes_output.len < nodes_input.len);

      nodes_input = nodes_output;

      pg_log(&logger, PG_LOG_LEVEL_DEBUG, "constant fold after",
             pg_log_c_u64("iteration", i));
      ast_print_nodes(nodes_input, &writer_internals, allocator);
    }
  }

  IrEmitter ir_emitter = {.errors = &errors, .src = lexer.src};

  PG_DYN(FnDefinition)
  fn_defs = ir_emit_from_ast(&ir_emitter, nodes_input, allocator);
  pg_log(&logger, PG_LOG_LEVEL_DEBUG, "IR",
         pg_log_c_u64("fn_defs_count", fn_defs.len));
  ir_print_fn_defs(fn_defs, &writer_internals, allocator);

  if (errors.len) {
    goto err;
  }

  PgString stem = pg_path_stem(cli_opts.file_path);
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
  asm_emit(&asm_emitter, fn_defs, &logger, allocator);

  pg_log(&logger, PG_LOG_LEVEL_DEBUG, "ASM",
         pg_log_c_s("file_path", asm_emitter.program.file_path));
  asm_print_program(asm_emitter, &writer_internals, allocator);

  PgError err_write = elf_write_exe(&asm_emitter, allocator);
  if (err_write) {
    pg_log(&logger, PG_LOG_LEVEL_ERROR, "failed to write to file",
           pg_log_c_err("err", err_write),
           pg_log_c_s("path", asm_emitter.program.file_path));
    return 1;
  }

  pg_log(&logger, PG_LOG_LEVEL_DEBUG, "arena stats",
         pg_log_c_u64("mem_use_bytes", pg_arena_mem_use(arena)),
         pg_log_c_u64("mem_available_bytes", pg_arena_mem_available(arena)));
  return 0;

err:
  // Errors could have been found at various stages so we sort them by order
  // of appearance in the file.
  qsort(errors.data, errors.len, sizeof(Error),
        err_compare_errors_by_origin_offset);

  PgWriter writer_errors = pg_writer_make_from_file_descriptor(
      pg_os_stderr(), 4 * PG_KiB, allocator);

  PG_EACH(err, errors) {
    origin_write(&writer_errors, err.origin, allocator);
    (void)pg_writer_write_full(&writer_errors, PG_S(" Error: "), allocator);
    error_print(err, &writer_errors, allocator);
  }
  (void)pg_writer_flush(&writer_errors, allocator);

  return 1;
}
