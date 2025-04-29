#include "ast.h"
#include "elf.h"
#include "error.h"
#include "ir.h"
#include "lex.h"
#include "submodules/cstd/lib.c"

typedef struct {
  bool verbose;
  bool optimize;
  char *filename;
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

  res.filename = argv[optind];

  return res;
}

int main(int argc, char *argv[]) {
  {
    GprSet gpr_set = {
        .len = 3,
        .set = (1 << 3) - 1,
    };
    PG_ASSERT(true == lir_gpr_is_set(gpr_set, 0));
    PG_ASSERT(true == lir_gpr_is_set(gpr_set, 1));
    PG_ASSERT(true == lir_gpr_is_set(gpr_set, 2));

    lir_gpr_set_remove(&gpr_set, 0);
    PG_ASSERT(false == lir_gpr_is_set(gpr_set, 0));

    lir_gpr_set_remove(&gpr_set, 2);
    PG_ASSERT(false == lir_gpr_is_set(gpr_set, 2));
    PG_ASSERT(0b010 == gpr_set.set);

    PG_ASSERT(1 == lir_gpr_pop_first_unset(&gpr_set).value);
    PG_ASSERT(0b11 == gpr_set.set);

    lir_gpr_set_add(&gpr_set, 0);
    lir_gpr_set_remove(&gpr_set, 1);
    lir_gpr_set_add(&gpr_set, 2);
    PG_ASSERT(0b101 == gpr_set.set);

    GprSet neighbors = {.len = 3, .set = 0b011};

    GprSet minus_res = lir_gpr_set_minus(gpr_set, neighbors);
    PG_ASSERT(0b100 == minus_res.set);
  }

  CliOptions cli_opts = cli_options_parse(argc, argv);

  PgArena arena = pg_arena_make_from_virtual_mem(16 * PG_MiB);
  PgArenaAllocator arena_allocator = pg_make_arena_allocator(&arena);
  PgAllocator *allocator = pg_arena_allocator_as_allocator(&arena_allocator);

  PgString file_name = pg_cstr_to_string(cli_opts.filename);
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
  if (cli_opts.verbose) {
    printf("\n------------ Lex tokens ------------\n");
    lex_tokens_print(tokens_slice);
  }

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

  if (cli_opts.verbose) {
    printf("\n------------ AST ------------\n");
    ast_print(*root, 0);
  }

  IrEmitter ir_emitter = {0};
  ast_to_ir(*root, &ir_emitter, &errors, false, allocator);
  if (errors.len) {
    for (u64 i = 0; i < errors.len; i++) {
      Error err = PG_SLICE_AT(errors, i);
      origin_print(err.origin);
      printf(" Error: ");
      error_print(err);
    }
    return 1;
  }

  if (cli_opts.verbose) {
    printf("\n------------ IR ------------\n");
    ir_emitter_print_instructions(ir_emitter);
  }
  if (cli_opts.optimize) {
    irs_optimize(&ir_emitter.instructions, &ir_emitter.lifetimes,
                 cli_opts.verbose);
    if (cli_opts.verbose) {
      printf("\n------------ IR simplified ------------\n");
      ir_emitter_print_instructions(ir_emitter);
    }
    ir_emitter_trim_tombstone_items(&ir_emitter);
  }
  if (cli_opts.verbose) {
    printf("\n------------ IR var lifetimes ------------\n");
    ir_emitter_print_var_lifetimes(ir_emitter);
  }

  IrInstructionSlice irs_slice =
      PG_DYN_SLICE(IrInstructionSlice, ir_emitter.instructions);

  LirVarInterferenceNodeDyn interference_graph_nodes = {0};
  if (ir_emitter.lifetimes.len > 0) {
    interference_graph_nodes =
        lir_build_var_interference_graph(ir_emitter.lifetimes, allocator);
  }
  LirVarInterferenceNodeSlice interference_graph_nodes_slice =
      PG_DYN_SLICE(LirVarInterferenceNodeSlice, interference_graph_nodes);

  if (cli_opts.verbose) {
    printf("\n------------ Interference graph ------------\n");
    lir_print_interference_nodes(interference_graph_nodes_slice);
  }
  lir_sanity_check_interference_graph(interference_graph_nodes_slice, false);

  LirEmitter lir_emitter = {
      .lifetimes_count = ir_emitter.lifetimes.len,
      .interference_nodes = interference_graph_nodes,
  };
  lir_emit_instructions(&lir_emitter, irs_slice, allocator);
  if (cli_opts.verbose) {
    printf("\n------------ LIR ------------\n");
    lir_emitter_print_instructions(lir_emitter);
  }
  LirInstructionSlice lirs_slice =
      PG_DYN_SLICE(LirInstructionSlice, lir_emitter.instructions);
  interference_graph_nodes_slice =
      PG_DYN_SLICE(LirVarInterferenceNodeSlice, lir_emitter.interference_nodes);

  Amd64Emitter amd64_emitter = {
      .interference_nodes = interference_graph_nodes_slice,
  };
  amd64_emit_prolog(&amd64_emitter.instructions, allocator);
  amd64_emit_lirs_to_asm(&amd64_emitter, lirs_slice, cli_opts.verbose,
                         allocator);
  amd64_emit_epilog(&amd64_emitter.instructions, allocator);

  if (cli_opts.verbose) {
    printf("\n------------ ASM ------------\n");
    amd64_print_instructions(
        PG_DYN_SLICE(Amd64InstructionSlice, amd64_emitter.instructions));
  }

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
      .instructions =
          PG_DYN_SLICE(Amd64InstructionSlice, amd64_emitter.instructions),
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

  if (cli_opts.verbose) {
    printf("arena: use=%lu available=%lu\n", pg_arena_mem_use(arena),
           pg_arena_mem_available(arena));
  }
}
