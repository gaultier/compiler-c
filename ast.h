#pragma once
#include "lex.h"

typedef enum {
  AST_NODE_KIND_NONE,
  AST_NODE_KIND_NUMBER,
  AST_NODE_KIND_IDENTIFIER,
  AST_NODE_KIND_ADD,
  AST_NODE_KIND_BLOCK,
  AST_NODE_KIND_VAR_DEFINITION,
  AST_NODE_KIND_ADDRESS_OF,
  AST_NODE_KIND_JUMP_IF_FALSE,
  AST_NODE_KIND_JUMP,
  AST_NODE_KIND_COMPARISON,
  AST_NODE_KIND_BUILTIN_ASSERT,
  AST_NODE_KIND_SYSCALL,
  AST_NODE_KIND_FN_DEFINITION,
  AST_NODE_KIND_LABEL_DEFINITION,
  AST_NODE_KIND_LABEL,
} AstNodeKind;

typedef struct AstNode AstNode;
PG_DYN(AstNode) AstNodeDyn;

typedef enum [[clang::flag_enum]] {
  AST_NODE_FLAG_NONE = 0,
  AST_NODE_FLAG_GLOBAL = 1 << 0,
  AST_NODE_FLAG_FN_NO_FRAME_POINTERS = 1 << 1,
} AstNodeFlag;

// Unresolved.
typedef struct {
  PgString value;
} Label;

typedef struct {
  u32 value;
} MetadataIndex;

struct AstNode {
  AstNodeKind kind;
  union {
    u64 n64;             // NUmber literal.
    PgString identifier; // Variable name.
    u32 args_count;      // Function, syscall, etc.
    Label label;
  } u;
  MetadataIndex meta_idx;
  Origin origin;
  LexTokenKind token_kind;
  AstNodeFlag flags;
};

typedef struct {
  u32 value;
} AstNodeIndex;
PG_DYN(AstNodeIndex) AstNodeIndexDyn;

typedef enum {
  VREG_CONSTRAINT_NONE,
  VREG_CONSTRAINT_CONDITION_FLAGS,
  VREG_CONSTRAINT_SYSCALL_NUM,
  VREG_CONSTRAINT_SYSCALL0,
  VREG_CONSTRAINT_SYSCALL1,
  VREG_CONSTRAINT_SYSCALL2,
  VREG_CONSTRAINT_SYSCALL3,
  VREG_CONSTRAINT_SYSCALL4,
  VREG_CONSTRAINT_SYSCALL5,
  VREG_CONSTRAINT_SYSCALL_RET,
} VirtualRegisterConstraint;

typedef struct {
  u32 value;
  VirtualRegisterConstraint constraint;
  bool addressable;
} VirtualRegister;
PG_DYN(VirtualRegister) VirtualRegisterDyn;

typedef struct {
  u32 value;
} Register;
PG_SLICE(Register) RegisterSlice;
PG_DYN(Register) RegisterDyn;

typedef enum {
  MEMORY_LOCATION_KIND_NONE,
  MEMORY_LOCATION_KIND_REGISTER,
  MEMORY_LOCATION_KIND_STACK,
  MEMORY_LOCATION_KIND_STATUS_REGISTER,
#if 0
  MEMORY_LOCATION_KIND_MEMORY,
#endif
} MemoryLocationKind;

typedef struct {
  MemoryLocationKind kind;
  union {
    Register reg;
    i32 base_pointer_offset;
#if 0
     u64 memory_address;
#endif
  } u;
} MemoryLocation;
PG_SLICE(MemoryLocation) MemoryLocationSlice;
PG_DYN(MemoryLocation) MemoryLocationDyn;

typedef struct {
  u32 value;
} InstructionIndex;

typedef struct {
  InstructionIndex lifetime_start, lifetime_end;
  VirtualRegister virtual_register;
  MemoryLocation memory_location;
  PgString identifier;
#if 0
  bool tombstone;
#endif
} Metadata;
PG_DYN(Metadata) MetadataDyn;

typedef struct {
  Lexer lexer;
  u64 tokens_consumed;
  ErrorDyn *errors;
  AstNodeDyn nodes;

  // Gets incremented.
  u32 label_id;

} AstParser;

typedef struct {
  MetadataDyn metadata;
  AstNodeIndex node_start, node_end;

  u32 stack_base_pointer_offset;
  u32 stack_base_pointer_offset_max;
} FnDefinition;
PG_DYN(FnDefinition) FnDefinitionDyn;

[[nodiscard]]
static Label ast_next_label_name(AstParser *parser, PgAllocator *allocator) {
  Label id = {
      .value = pg_u64_to_string(++parser->label_id, allocator),
  };
  return id;
}

static void ast_add_error(AstParser *parser, ErrorKind error_kind,
                          Origin origin, PgAllocator *allocator) {
  *PG_DYN_PUSH(parser->errors, allocator) = (Error){
      .kind = error_kind,
      .origin = origin,
      .src = parser->lexer.src,
      // FIXME
      .src_span = PG_SLICE_RANGE(parser->lexer.src, origin.file_offset_start,
                                 origin.file_offset_start + 1),
  };

  // Skip to the next newline to avoid having cascading errors.

  for (; parser->tokens_consumed < parser->lexer.tokens.len;
       parser->tokens_consumed++) {
    LexToken token = PG_SLICE_AT(parser->lexer.tokens, parser->tokens_consumed);
    if (token.origin.line > origin.line) {
      break;
    }
  }
}

// Best effort to find the closest token when doing error reporting.
[[nodiscard]]
static LexToken ast_current_or_last_token(AstParser parser) {
  LexToken res = {0};

  if (parser.tokens_consumed >= parser.lexer.tokens.len) {
    return PG_DYN_LAST(parser.lexer.tokens);
  }

  res = PG_SLICE_AT(parser.lexer.tokens, parser.tokens_consumed);
  if (res.kind) {
    return res;
  }

  return PG_SLICE_AT(parser.lexer.tokens,
                     parser.tokens_consumed ? parser.tokens_consumed - 1 : 0);
}

static void ast_push(AstParser *parser, AstNode node, PgAllocator *allocator) {
  *PG_DYN_PUSH(&parser->nodes, allocator) = node;
}

[[maybe_unused]] // TODO
[[nodiscard]]
static AstNode ast_pop_first(AstNodeDyn nodes, u64 *idx) {
  PG_ASSERT(idx);

  AstNode res = {0};

  if (*idx >= nodes.len) {
    return res;
  }

  res = PG_SLICE_AT(nodes, *idx);
  *idx += 1;

  return res;
}

static void print_var(Metadata meta) {
  if (0 == meta.virtual_register.value) {
    return;
  }

  if (!pg_string_is_empty(meta.identifier)) {
    printf("%.*s%%%" PRIu32, (i32)meta.identifier.len, meta.identifier.data,
           meta.virtual_register.value);
  } else {
    printf("%%%" PRIu32, meta.virtual_register.value);
  }
}

[[nodiscard]]
static char *register_constraint_to_cstr(VirtualRegisterConstraint constraint) {
  switch (constraint) {
  case VREG_CONSTRAINT_NONE:
    return "NONE";
  case VREG_CONSTRAINT_CONDITION_FLAGS:
    return "CONDITION_FLAGS";
  case VREG_CONSTRAINT_SYSCALL_NUM:
    return "SYSCALL_NUM";
  case VREG_CONSTRAINT_SYSCALL0:
    return "SYSCALL0";
  case VREG_CONSTRAINT_SYSCALL1:
    return "SYSCALL1";
  case VREG_CONSTRAINT_SYSCALL2:
    return "SYSCALL2";
  case VREG_CONSTRAINT_SYSCALL3:
    return "SYSCALL3";
  case VREG_CONSTRAINT_SYSCALL4:
    return "SYSCALL4";
  case VREG_CONSTRAINT_SYSCALL5:
    return "SYSCALL5";
  case VREG_CONSTRAINT_SYSCALL_RET:
    return "SYSCALL_RET";

  default:
    PG_ASSERT(0);
  }
}

static void metadata_print_meta(Metadata meta) {
#if 0
  if (meta.tombstone) {
    printf("\x1B[9m"); // Strikethrough.
  }
#endif

  printf("var=");
  print_var(meta);
  printf(" lifetime=[%u:%u]", meta.lifetime_start.value,
         meta.lifetime_end.value);

  if (meta.virtual_register.value) {
    printf(" vreg=v%u{constraint=%s, addressable=%s}",
           meta.virtual_register.value,
           register_constraint_to_cstr(meta.virtual_register.constraint),
           meta.virtual_register.addressable ? "true" : "false");
  }

  if (MEMORY_LOCATION_KIND_NONE != meta.memory_location.kind) {
    printf(" mem_loc=");

    switch (meta.memory_location.kind) {
    case MEMORY_LOCATION_KIND_REGISTER:
    case MEMORY_LOCATION_KIND_STATUS_REGISTER:
      printf("reg(todo)");
      // TODO
#if 0
      amd64_print_register(meta.memory_location.reg);
#endif
      break;
    case MEMORY_LOCATION_KIND_STACK: {
      printf("[sp");
      i32 offset = meta.memory_location.u.base_pointer_offset;
      printf("-%" PRIi32 "]", offset);
    } break;
#if 0
    case MEMORY_LOCATION_KIND_MEMORY:
      printf("%#lx", loc.memory_address);
      break;
#endif
    case MEMORY_LOCATION_KIND_NONE:
    default:
      PG_ASSERT(0);
    }
  }

#if 0
  if (meta.tombstone) {
    printf("\x1B[0m"); // Strikethrough.
  }
#endif
}

static void ast_print(AstNodeDyn nodes, MetadataDyn metadata, u32 left_width) {
  for (u32 i = 0; i < nodes.len; i++) {
    printf("[%u] ", i);
    AstNode node = PG_SLICE_AT(nodes, i);

    for (u64 j = 0; j < left_width; j++) {
      putchar(' ');
    }
    origin_print(node.origin);
    putchar(' ');

    switch (node.kind) {
    case AST_NODE_KIND_NUMBER:
      printf("U64 %" PRIu64, node.u.n64);
      break;
    case AST_NODE_KIND_IDENTIFIER:
      printf("Identifier %.*s", (i32)node.u.identifier.len,
             node.u.identifier.data);
      break;
    case AST_NODE_KIND_ADDRESS_OF:
      printf("AddressOf");
      break;
    case AST_NODE_KIND_BUILTIN_ASSERT:
      printf("Assert");
      break;
    case AST_NODE_KIND_ADD:
      printf("Add");
      break;
    case AST_NODE_KIND_COMPARISON:
      printf("Comparison");
      break;
    case AST_NODE_KIND_SYSCALL: {
      printf("Syscall");
    } break;
    case AST_NODE_KIND_BLOCK: {
      printf("Block");
    } break;
    case AST_NODE_KIND_VAR_DEFINITION:
      printf("VarDecl %.*s", (i32)node.u.identifier.len,
             node.u.identifier.data);
      break;
    case AST_NODE_KIND_JUMP_IF_FALSE:
      printf("JumpIfFalse");
      break;
    case AST_NODE_KIND_JUMP:
      printf("Jump");
      break;
    case AST_NODE_KIND_FN_DEFINITION:
      printf("FnDefinition %.*s", (i32)node.u.identifier.len,
             node.u.identifier.data);
      break;
    case AST_NODE_KIND_LABEL_DEFINITION:
      printf("LabelDefinition %.*s", (i32)node.u.label.value.len,
             node.u.label.value.data);
      break;
    case AST_NODE_KIND_LABEL:
      printf("Label %.*s", (i32)node.u.label.value.len,
             node.u.label.value.data);
      break;
    case AST_NODE_KIND_NONE:
    default:
      PG_ASSERT(0);
    }
    if (metadata.len && node.meta_idx.value) {
      printf(" // ");
      Metadata meta = PG_SLICE_AT(metadata, node.meta_idx.value);
      metadata_print_meta(meta);
    }
    printf("\n");
  }
}

[[nodiscard]]
static LexToken ast_match_token_kind(AstParser *parser, LexTokenKind kind) {
  LexToken res = {0};

  if (parser->tokens_consumed >= parser->lexer.tokens.len) {
    return res;
  }

  LexToken token = PG_SLICE_AT(parser->lexer.tokens, parser->tokens_consumed);
  if (kind != token.kind) {
    return res;
  }

  parser->tokens_consumed += 1;
  res = token;
  return res;
}

[[nodiscard]]
static LexToken ast_match_token_kind1_or_kind2(AstParser *parser,
                                               LexTokenKind kind1,
                                               LexTokenKind kind2) {
  LexToken res = {0};

  if (parser->tokens_consumed >= parser->lexer.tokens.len) {
    return res;
  }

  LexToken token = PG_SLICE_AT(parser->lexer.tokens, parser->tokens_consumed);
  if (!(kind1 == token.kind || kind2 == token.kind)) {
    return res;
  }

  parser->tokens_consumed += 1;
  res = token;
  return res;
}

[[nodiscard]]
static bool ast_parse_expr(AstParser *parser, PgAllocator *allocator);
[[nodiscard]]
static bool ast_parse_statement(AstParser *parser, PgAllocator *allocator);
[[nodiscard]]
static bool ast_parse_declaration(AstParser *parser, PgAllocator *allocator);
[[nodiscard]]
static bool ast_parse_syscall(AstParser *parser, PgAllocator *allocator);

[[nodiscard]]
static bool ast_parse_var_decl(AstParser *parser, PgAllocator *allocator) {
  LexToken token_first =
      ast_match_token_kind(parser, LEX_TOKEN_KIND_IDENTIFIER);
  if (!token_first.kind) {
    return false;
  }
  PG_ASSERT(!pg_string_is_empty(token_first.s));

  LexToken token_colon_equal =
      ast_match_token_kind(parser, LEX_TOKEN_KIND_COLON_EQUAL);
  if (!token_colon_equal.kind) {
    ast_add_error(parser, ERROR_KIND_PARSE_VAR_DECL_MISSING_COLON_EQUAL,
                  ast_current_or_last_token(*parser).origin, allocator);
    return false;
  }

  if (!ast_parse_expr(parser, allocator)) {
    ast_add_error(parser, ERROR_KIND_PARSE_VAR_DECL_MISSING_VALUE,
                  ast_current_or_last_token(*parser).origin, allocator);
    return false;
  }

  AstNode node = {0};
  node.kind = AST_NODE_KIND_VAR_DEFINITION;
  node.origin = token_first.origin;
  node.u.identifier = token_first.s;
  ast_push(parser, node, allocator);

  return true;
}

[[nodiscard]]
static bool ast_parse_primary(AstParser *parser, PgAllocator *allocator) {
  LexToken first = ast_match_token_kind1_or_kind2(
      parser, LEX_TOKEN_KIND_LITERAL_NUMBER, LEX_TOKEN_KIND_IDENTIFIER);

  if (LEX_TOKEN_KIND_LITERAL_NUMBER == first.kind) {
    AstNode node = {0};
    node.origin = first.origin;
    node.kind = AST_NODE_KIND_NUMBER;
    PgParseNumberResult parse_res = pg_string_parse_u64(first.s);
    PG_ASSERT(parse_res.present);
    PG_ASSERT(pg_string_is_empty(parse_res.remaining));
    node.u.n64 = parse_res.n;
    ast_push(parser, node, allocator);

    return true;
  }

  if (LEX_TOKEN_KIND_IDENTIFIER == first.kind) {
    AstNode node = {0};
    node.origin = first.origin;
    node.kind = AST_NODE_KIND_IDENTIFIER;
    node.u.identifier = first.s;
    ast_push(parser, node, allocator);

    return true;
  }

  return false;
}

[[nodiscard]]
static bool ast_parse_call(AstParser *parser, PgAllocator *allocator) {
  return ast_parse_primary(parser, allocator);
}

[[nodiscard]]
static bool ast_parse_unary(AstParser *parser, PgAllocator *allocator) {
  LexToken token_first = ast_match_token_kind(parser, LEX_TOKEN_KIND_AMPERSAND);
  if (!token_first.kind) {
    return ast_parse_call(parser, allocator);
  }

  if (!ast_parse_unary(parser, allocator)) {
    ast_add_error(parser, ERROR_KIND_PARSE_UNARY_MISSING_RHS,
                  ast_current_or_last_token(*parser).origin, allocator);
    return false;
  }

  AstNode node = {0};
  node.origin = token_first.origin;
  node.kind = AST_NODE_KIND_ADDRESS_OF;
  ast_push(parser, node, allocator);

  return true;
}

[[nodiscard]]
static bool ast_parse_factor(AstParser *parser, PgAllocator *allocator) {
  return ast_parse_unary(parser, allocator);
}

[[nodiscard]]
static bool ast_parse_term(AstParser *parser, PgAllocator *allocator) {
  if (!ast_parse_factor(parser, allocator)) {
    return false;
  }

  for (u64 _i = parser->tokens_consumed; _i < parser->lexer.tokens.len; _i++) {
    LexToken token = ast_match_token_kind(parser, LEX_TOKEN_KIND_PLUS);
    if (!token.kind) {
      return true;
    }

    if (!ast_parse_factor(parser, allocator)) {
      ast_add_error(parser, ERROR_KIND_PARSE_FACTOR_MISSING_RHS,
                    ast_current_or_last_token(*parser).origin, allocator);
      return false;
    }
    AstNode node = {0};
    node.origin = token.origin;
    node.kind = AST_NODE_KIND_ADD;
    ast_push(parser, node, allocator);
  }
  return ast_match_token_kind(parser, LEX_TOKEN_KIND_EOF).kind !=
         LEX_TOKEN_KIND_NONE;
}

[[nodiscard]]
static bool ast_parse_comparison(AstParser *parser, PgAllocator *allocator) {
  return ast_parse_term(parser, allocator);
}

[[nodiscard]]
static bool ast_parse_equality(AstParser *parser, PgAllocator *allocator) {
  if (!ast_parse_comparison(parser, allocator)) {
    return false;
  }

  for (u64 _i = parser->tokens_consumed; _i < parser->lexer.tokens.len; _i++) {
    LexToken token = ast_match_token_kind(parser, LEX_TOKEN_KIND_EQUAL_EQUAL);
    // TODO: `!=`.
    if (!token.kind) {
      return true;
    }
    if (!ast_parse_comparison(parser, allocator)) {
      ast_add_error(parser, ERROR_KIND_PARSE_EQUALITY_MISSING_RHS,
                    ast_current_or_last_token(*parser).origin, allocator);
      return false;
    }

    AstNode node = {0};
    node.origin = token.origin;
    node.kind = AST_NODE_KIND_COMPARISON;
    node.token_kind = token.kind;
    ast_push(parser, node, allocator);
  }
  return ast_match_token_kind(parser, LEX_TOKEN_KIND_EOF).kind !=
         LEX_TOKEN_KIND_NONE;
}

[[nodiscard]]
static bool ast_parse_logic_and(AstParser *parser, PgAllocator *allocator) {
  return ast_parse_equality(parser, allocator);
}

[[nodiscard]]
static bool ast_parse_logic_or(AstParser *parser, PgAllocator *allocator) {
  return ast_parse_logic_and(parser, allocator);
}

[[nodiscard]]
static bool ast_parse_assignment(AstParser *parser, PgAllocator *allocator) {
  return ast_parse_logic_or(parser, allocator);
}

[[nodiscard]]
static bool ast_parse_expr(AstParser *parser, PgAllocator *allocator) {
  if (ast_parse_syscall(parser, allocator)) {
    return true;
  }

  if (ast_parse_assignment(parser, allocator)) {
    return true;
  }

  return false;
}

[[nodiscard]]
static bool ast_parse_syscall(AstParser *parser, PgAllocator *allocator) {
  LexToken token_first =
      ast_match_token_kind(parser, LEX_TOKEN_KIND_KEYWORD_SYSCALL);
  if (!token_first.kind) {
    return false;
  }

  LexToken token_left_paren =
      ast_match_token_kind(parser, LEX_TOKEN_KIND_PAREN_LEFT);
  if (!token_left_paren.kind) {
    ast_add_error(parser, ERROR_KIND_PARSE_MISSING_PAREN_LEFT,
                  ast_current_or_last_token(*parser).origin, allocator);
    return false;
  }

  LexToken token_after = {0};

  u32 args_count = 0;

  while (parser->tokens_consumed < parser->lexer.tokens.len) {
    LexToken token = PG_SLICE_AT(parser->lexer.tokens, parser->tokens_consumed);
    if (LEX_TOKEN_KIND_PAREN_RIGHT == token.kind) {
      break;
    }

    if (!ast_parse_expr(parser, allocator)) {
      ast_add_error(parser, ERROR_KIND_PARSE_SYSCALL_MISSING_OPERAND,
                    ast_current_or_last_token(*parser).origin, allocator);
      return false;
    }

    args_count += 1;

    token_after = ast_match_token_kind1_or_kind2(
        parser, LEX_TOKEN_KIND_PAREN_RIGHT, LEX_TOKEN_KIND_COMMA);
    if (LEX_TOKEN_KIND_PAREN_RIGHT == token_after.kind) {
      break;
    }
    if (LEX_TOKEN_KIND_COMMA == token_after.kind) {
      continue;
    }

    ast_add_error(parser, ERROR_KIND_PARSE_SYSCALL_MISSING_COMMA,
                  ast_current_or_last_token(*parser).origin, allocator);
    return false;
  }

  if (LEX_TOKEN_KIND_PAREN_RIGHT != token_after.kind) {
    ast_add_error(parser, ERROR_KIND_PARSE_MISSING_PAREN_RIGHT,
                  ast_current_or_last_token(*parser).origin, allocator);
    return false;
  }

  AstNode node = {0};
  node.origin = token_first.origin;
  node.kind = AST_NODE_KIND_SYSCALL;
  node.u.args_count = args_count;
  ast_push(parser, node, allocator);

  return true;
}

[[nodiscard]]
static bool ast_parse_block(AstParser *parser, PgAllocator *allocator) {
  LexToken token_first =
      ast_match_token_kind(parser, LEX_TOKEN_KIND_CURLY_LEFT);
  if (!token_first.kind) {
    return false;
  }

  u32 args_count = 0;

  for (u64 _i = parser->tokens_consumed; _i < parser->lexer.tokens.len; _i++) {
    LexToken token = ast_match_token_kind(parser, LEX_TOKEN_KIND_CURLY_RIGHT);
    if (token.kind) {
      AstNode node = {0};
      node.origin = token_first.origin;
      node.kind = AST_NODE_KIND_BLOCK;
      node.u.args_count = args_count;
      return true;
    }

    if (!ast_parse_declaration(parser, allocator)) {
      break; // EOF?
    }
  }

  ast_add_error(parser, ERROR_KIND_PARSE_BLOCK_MISSING_CURLY_RIGHT,
                ast_current_or_last_token(*parser).origin, allocator);
  return false;
}

[[nodiscard]]
static bool ast_parse_statement_if(AstParser *parser, PgAllocator *allocator) {
  LexToken token_first =
      ast_match_token_kind(parser, LEX_TOKEN_KIND_KEYWORD_IF);
  if (!token_first.kind) {
    return false;
  }

  if (!ast_parse_expr(parser, allocator)) {
    ast_add_error(parser, ERROR_KIND_PARSE_IF_MISSING_CONDITION,
                  ast_current_or_last_token(*parser).origin, allocator);
    return false;
  }

  Label branch_else_label = ast_next_label_name(parser, allocator);
  Label branch_if_cont_label = ast_next_label_name(parser, allocator);

  {
    AstNode jump_else_label = {0};
    jump_else_label.kind = AST_NODE_KIND_LABEL;
    jump_else_label.u.label = branch_else_label;
    ast_push(parser, jump_else_label, allocator);

    AstNode jump_if_false = {0};
    jump_if_false.kind = AST_NODE_KIND_JUMP_IF_FALSE;
    jump_if_false.u.label = branch_else_label;
    ast_push(parser, jump_if_false, allocator);
  }

  if (!ast_parse_block(parser, allocator)) {
    ast_add_error(parser, ERROR_KIND_PARSE_IF_MISSING_THEN_BLOCK,
                  token_first.origin, allocator);
    return false;
  }

  {
    AstNode jump_if_cont_label = {0};
    jump_if_cont_label.kind = AST_NODE_KIND_LABEL;
    jump_if_cont_label.u.label = branch_if_cont_label;
    ast_push(parser, jump_if_cont_label, allocator);

    AstNode jump = {0};
    jump.kind = AST_NODE_KIND_JUMP;
    jump.u.label = branch_if_cont_label;
    ast_push(parser, jump, allocator);
  }

  AstNode jump_else_label_def = {0};
  jump_else_label_def.kind = AST_NODE_KIND_LABEL_DEFINITION;
  jump_else_label_def.u.label = branch_else_label;
  ast_push(parser, jump_else_label_def, allocator);

  // TODO: optional else.

  AstNode jump_if_cont_label_def = {0};
  jump_if_cont_label_def.kind = AST_NODE_KIND_LABEL_DEFINITION;
  jump_if_cont_label_def.u.label = branch_if_cont_label;
  ast_push(parser, jump_if_cont_label_def, allocator);

  return true;
}

[[nodiscard]]
static bool ast_parse_statement_assert(AstParser *parser,
                                       PgAllocator *allocator) {
  LexToken token_first =
      ast_match_token_kind(parser, LEX_TOKEN_KIND_KEYWORD_ASSERT);
  if (!token_first.kind) {
    return false;
  }

  LexToken token_paren_left =
      ast_match_token_kind(parser, LEX_TOKEN_KIND_PAREN_LEFT);
  if (!token_paren_left.kind) {
    ast_add_error(parser, ERROR_KIND_PARSE_MISSING_PAREN_LEFT,
                  ast_current_or_last_token(*parser).origin, allocator);
    return false;
  }

  if (!ast_parse_expr(parser, allocator)) {
    ast_add_error(parser, ERROR_KIND_PARSE_ASSERT_MISSING_EXPRESSION,
                  ast_current_or_last_token(*parser).origin, allocator);
    return false;
  }

  LexToken token_paren_right =
      ast_match_token_kind(parser, LEX_TOKEN_KIND_PAREN_RIGHT);
  if (!token_paren_right.kind) {
    ast_add_error(parser, ERROR_KIND_PARSE_MISSING_PAREN_RIGHT,
                  ast_current_or_last_token(*parser).origin, allocator);
    return false;
  }

  AstNode node = {0};
  node.origin = token_first.origin;
  node.kind = AST_NODE_KIND_BUILTIN_ASSERT;
  ast_push(parser, node, allocator);

  return true;
}

[[nodiscard]]
static bool ast_parse_statement(AstParser *parser, PgAllocator *allocator) {
  if (ast_parse_statement_if(parser, allocator)) {
    return true;
  }

  if (ast_parse_statement_assert(parser, allocator)) {
    return true;
  }

  if (ast_parse_expr(parser, allocator)) {
    return true;
  }

  return false;
}

[[nodiscard]]
static bool ast_parse_declaration(AstParser *parser, PgAllocator *allocator) {
  if (ast_parse_var_decl(parser, allocator)) {
    return true;
  }

  return ast_parse_statement(parser, allocator);
}

static void ast_emit_program_epilog(AstParser *parser, PgAllocator *allocator) {
  {
    AstNode fn = {0};
    fn.kind = AST_NODE_KIND_FN_DEFINITION;
    fn.u.identifier = PG_S("__builtin_exit");
    fn.flags = AST_NODE_FLAG_FN_NO_FRAME_POINTERS;
    ast_push(parser, fn, allocator);

    AstNode op0 = {0};
    op0.kind = AST_NODE_KIND_NUMBER;
    op0.u.n64 = 60; // FIXME: Only on Linux amd64.
    ast_push(parser, op0, allocator);

    AstNode op1 = {0};
    op1.kind = AST_NODE_KIND_NUMBER;
    op1.u.n64 = 0;
    ast_push(parser, op1, allocator);

    AstNode syscall = {0};
    syscall.kind = AST_NODE_KIND_SYSCALL;
    ast_push(parser, syscall, allocator);
  }
  {
    AstNode fn = {0};
    fn.kind = AST_NODE_KIND_FN_DEFINITION;
    fn.u.identifier = PG_S("__builtin_die");
    fn.flags = AST_NODE_FLAG_FN_NO_FRAME_POINTERS;
    ast_push(parser, fn, allocator);

    AstNode op0 = {0};
    op0.kind = AST_NODE_KIND_NUMBER;
    op0.u.n64 = 60; // FIXME: Only on Linux amd64.
    ast_push(parser, op0, allocator);

    AstNode op1 = {0};
    op1.kind = AST_NODE_KIND_NUMBER;
    op1.u.n64 = 1;
    ast_push(parser, op1, allocator);

    AstNode syscall = {0};
    syscall.kind = AST_NODE_KIND_SYSCALL;
    ast_push(parser, syscall, allocator);
  }
}

static void ast_emit(AstParser *parser, PgAllocator *allocator) {
  AstNode fn_start = {0};
  fn_start.kind = AST_NODE_KIND_FN_DEFINITION;
  fn_start.u.identifier = PG_S("_start");
  fn_start.flags = AST_NODE_FLAG_GLOBAL;
  // TODO: Do not define this function to avoid recursive calls to it.
  ast_push(parser, fn_start, allocator);

  for (u64 _i = 0; _i < parser->lexer.tokens.len;) {
    if (ast_match_token_kind(parser, LEX_TOKEN_KIND_EOF).kind) {
      break;
    }

    if (!ast_parse_declaration(parser, allocator)) {
      continue;
    }
  }

  ast_emit_program_epilog(parser, allocator);
}

[[nodiscard]] static MetadataIndex metadata_last_idx(MetadataDyn metadata) {
  PG_ASSERT(metadata.len > 0);
  return (MetadataIndex){(u32)metadata.len - 1};
}

[[nodiscard]]
static MetadataIndex metadata_make(MetadataDyn *metadata,
                                   PgAllocator *allocator) {
  Metadata res = {0};
  res.virtual_register.value = (u32)metadata->len;

  *PG_DYN_PUSH(metadata, allocator) = res;

  return metadata_last_idx(*metadata);
}

static void metadata_start_lifetime(MetadataDyn metadata,
                                    MetadataIndex meta_idx,
                                    InstructionIndex ins_idx) {
  PG_SLICE_AT(metadata, meta_idx.value).lifetime_start = ins_idx;
  PG_SLICE_AT(metadata, meta_idx.value).lifetime_end = ins_idx;
}

[[maybe_unused]] [[nodiscard]]
static MetadataIndex metadata_ptr_to_idx(MetadataDyn metadata, Metadata *meta) {
  return (MetadataIndex){(u32)(meta - metadata.data)};
}

[[nodiscard]]
static Metadata *metadata_find_by_identifier(MetadataDyn metadata,
                                             PgString identifier) {
  for (u64 i = 0; i < metadata.len; i++) {
    Metadata *meta = PG_SLICE_AT_PTR(&metadata, i);
    if (pg_string_eq(meta->identifier, identifier)) {
      return meta;
    }
  }
  return nullptr;
}

static void metadata_extend_lifetime_on_use(MetadataDyn metadata,
                                            MetadataIndex meta_idx,
                                            InstructionIndex ins_idx) {
  PG_SLICE_AT(metadata, meta_idx.value).lifetime_end = ins_idx;

  // TODO: Variable pointed to needs to live at least as long as the pointer to
  // it.
  // TODO: If there are multiple aliases to the same pointer, all aliases
  // should have their meta extended to this point!
  // TODO: Dataflow.
}

[[nodiscard]] static u32 ast_node_get_expected_args_count(AstNode node) {
  switch (node.kind) {
  case AST_NODE_KIND_NUMBER:
  case AST_NODE_KIND_IDENTIFIER:
  case AST_NODE_KIND_FN_DEFINITION:
  case AST_NODE_KIND_LABEL_DEFINITION:
  case AST_NODE_KIND_LABEL:
    return 0;

  case AST_NODE_KIND_ADDRESS_OF:
  case AST_NODE_KIND_VAR_DEFINITION:
  case AST_NODE_KIND_JUMP:
  case AST_NODE_KIND_BUILTIN_ASSERT:
    return 1;

  case AST_NODE_KIND_ADD:
  case AST_NODE_KIND_COMPARISON:
  case AST_NODE_KIND_JUMP_IF_FALSE:
    return 2;

  case AST_NODE_KIND_BLOCK:
  case AST_NODE_KIND_SYSCALL:
    return node.u.args_count;

  case AST_NODE_KIND_NONE:
  default:
    PG_ASSERT(0);
  }
}

[[nodiscard]] static bool ast_node_has_name(AstNode node) {
  switch (node.kind) {
  case AST_NODE_KIND_IDENTIFIER:
  case AST_NODE_KIND_FN_DEFINITION:
  case AST_NODE_KIND_VAR_DEFINITION:
  case AST_NODE_KIND_LABEL_DEFINITION:
    return true;

  case AST_NODE_KIND_ADDRESS_OF:
  case AST_NODE_KIND_JUMP:
  case AST_NODE_KIND_NUMBER:
  case AST_NODE_KIND_LABEL:
  case AST_NODE_KIND_BUILTIN_ASSERT:
  case AST_NODE_KIND_ADD:
  case AST_NODE_KIND_COMPARISON:
  case AST_NODE_KIND_JUMP_IF_FALSE:
  case AST_NODE_KIND_BLOCK:
  case AST_NODE_KIND_SYSCALL:
    return false;

  case AST_NODE_KIND_NONE:
  default:
    PG_ASSERT(0);
  }
}

[[nodiscard]] static bool ast_node_is_kind_addressable(AstNode node) {
  switch (node.kind) {
  case AST_NODE_KIND_IDENTIFIER:
  case AST_NODE_KIND_ADDRESS_OF:
    return true;

  case AST_NODE_KIND_FN_DEFINITION:
  case AST_NODE_KIND_VAR_DEFINITION:
  case AST_NODE_KIND_LABEL_DEFINITION:
  case AST_NODE_KIND_JUMP:
  case AST_NODE_KIND_NUMBER:
  case AST_NODE_KIND_LABEL:
  case AST_NODE_KIND_BUILTIN_ASSERT:
  case AST_NODE_KIND_ADD:
  case AST_NODE_KIND_COMPARISON:
  case AST_NODE_KIND_JUMP_IF_FALSE:
  case AST_NODE_KIND_BLOCK:
  case AST_NODE_KIND_SYSCALL:
    return false;

  case AST_NODE_KIND_NONE:
  default:
    PG_ASSERT(0);
  }
}

[[nodiscard]] static bool ast_node_is_expr(AstNode node) {
  switch (node.kind) {
  case AST_NODE_KIND_IDENTIFIER:
  case AST_NODE_KIND_NUMBER:
  case AST_NODE_KIND_ADD:
  case AST_NODE_KIND_COMPARISON:
  case AST_NODE_KIND_ADDRESS_OF:
  case AST_NODE_KIND_SYSCALL:
    return true;

  case AST_NODE_KIND_JUMP:
  case AST_NODE_KIND_FN_DEFINITION:
  case AST_NODE_KIND_VAR_DEFINITION:
  case AST_NODE_KIND_LABEL_DEFINITION:
  case AST_NODE_KIND_LABEL:
  case AST_NODE_KIND_BUILTIN_ASSERT:
  case AST_NODE_KIND_JUMP_IF_FALSE:
  case AST_NODE_KIND_BLOCK:
    return false;

  case AST_NODE_KIND_NONE:
  default:
    PG_ASSERT(0);
  }
}

static void ast_stack_push(AstNodeIndexDyn *stack, AstNodeIndex node_idx,
                           PgAllocator *allocator) {
  *PG_DYN_PUSH(stack, allocator) = node_idx;
  printf("[D001] push node_idx=%u stack_len=%lu\n", node_idx.value, stack->len);
}

[[nodiscard]]
static AstNodeIndex ast_stack_pop(AstNodeIndexDyn *stack) {
  PG_ASSERT(stack->len);
  AstNodeIndex res = PG_SLICE_LAST(*stack);
  stack->len -= 1;
  printf("[D001] pop node_idx=%u stack_len=%lu\n", res.value, stack->len);
  return res;
}

[[nodiscard]]
static FnDefinitionDyn ast_generate_metadata(AstParser *parser,
                                             PgAllocator *allocator) {

  AstNodeIndexDyn stack = {0};
  PG_DYN_ENSURE_CAP(&stack, 512, allocator);

  FnDefinitionDyn fn_defs = {0};
  u32 fn_idx = 0;

  for (u32 i = 0; i < parser->nodes.len; i++) {
    InstructionIndex ins_idx = {i};
    AstNode *node = PG_SLICE_AT_PTR(&parser->nodes, i);
    AstNodeIndex node_idx = {i};
    bool is_expr = ast_node_is_expr(*node);

    FnDefinition *fn_def =
        fn_idx < fn_defs.len ? PG_SLICE_AT_PTR(&fn_defs, fn_idx) : nullptr;

    if (is_expr) {
      node->meta_idx = metadata_make(&fn_def->metadata, allocator);
      metadata_start_lifetime(fn_def->metadata, node->meta_idx, ins_idx);

      if (ast_node_has_name(*node)) {
        PG_ASSERT(node->u.identifier.len);
        PG_DYN_LAST(fn_def->metadata).identifier = node->u.identifier;
      }
    }

    if (AST_NODE_KIND_ADDRESS_OF == node->kind) {
    }

    // Specific actions.
    switch (node->kind) {
    case AST_NODE_KIND_IDENTIFIER: {
      // Here the variable name is resolved.
      // TODO: Scope aware symbol resolution.
      Metadata *meta =
          metadata_find_by_identifier(fn_def->metadata, node->u.identifier);
      if (!meta) {
        ast_add_error(parser, ERROR_KIND_UNDEFINED_VAR, node->origin,
                      allocator);
        PG_DYN_LAST(*parser->errors).src_span = node->u.identifier;
      }
    } break;

    case AST_NODE_KIND_FN_DEFINITION: {
      FnDefinition fn_def_new = {.node_start = node_idx};
      // TODO: Still needed?
      *PG_DYN_PUSH(&fn_def_new.metadata, allocator) = (Metadata){0}; // Dummy.

      *PG_DYN_PUSH(&fn_defs, allocator) = fn_def_new;
      fn_idx = (u32)fn_defs.len - 1;
    } break;

    case AST_NODE_KIND_ADDRESS_OF:
    case AST_NODE_KIND_SYSCALL:
    case AST_NODE_KIND_NUMBER:
    case AST_NODE_KIND_ADD:
    case AST_NODE_KIND_COMPARISON:
    case AST_NODE_KIND_VAR_DEFINITION:
    case AST_NODE_KIND_LABEL_DEFINITION:
    case AST_NODE_KIND_LABEL:
    case AST_NODE_KIND_JUMP_IF_FALSE:
    case AST_NODE_KIND_JUMP:
    case AST_NODE_KIND_BUILTIN_ASSERT:
    case AST_NODE_KIND_BLOCK:
      break;

    case AST_NODE_KIND_NONE:
    default:
      PG_ASSERT(0);
    }

    // Stack.
    {
      if (AST_NODE_KIND_FN_DEFINITION == node->kind) {
        stack.len = 0;
      }

      u32 args_count = ast_node_get_expected_args_count(*node);
      if (!(stack.len >= args_count)) {
        ast_add_error(parser, ERROR_KIND_WRONG_ARGS_COUNT, node->origin,
                      allocator);
        continue;
      }
      for (u32 j = 0; j < args_count; j++) {
        AstNodeIndex top_idx = ast_stack_pop(&stack);
        AstNode top = PG_SLICE_AT(parser->nodes, top_idx.value);

        if (AST_NODE_KIND_ADDRESS_OF == node->kind) {
          if (!ast_node_is_kind_addressable(top)) {
            ast_add_error(parser, ERROR_KIND_ADDRESS_OF_RHS_NOT_ADDRESSABLE,
                          node->origin, allocator);
            continue;
          }

          PG_SLICE_AT(fn_def->metadata, top.meta_idx.value)
              .virtual_register.addressable = true;
        }

        metadata_extend_lifetime_on_use(fn_def->metadata, top.meta_idx,
                                        ins_idx);
      }

      // Stack push.
      if (is_expr) {
        ast_stack_push(&stack, node_idx, allocator);
      }
      if (!is_expr && stack.len > 0) {
        ast_add_error(parser, ERROR_KIND_MALFORMED_AST, node->origin,
                      allocator);
        PG_ASSERT(0);
      }
    }
  }

  return fn_defs;
}

static void ast_print_fn_defs(FnDefinitionDyn fn_defs, AstNodeDyn nodes) {
  for (u32 i = 0; i < fn_defs.len; i++) {
    FnDefinition fn_def = PG_SLICE_AT(fn_defs, i);
    AstNode fn_node = PG_SLICE_AT(nodes, fn_def.node_start.value);

    printf("%.*s:\n", (i32)fn_node.u.identifier.len, fn_node.u.identifier.data);

    for (u32 j = 0; j < fn_def.metadata.len; j++) {
      Metadata meta = PG_SLICE_AT(fn_def.metadata, j);

      metadata_print_meta(meta);
      printf("\n");
    }
    printf("\n");
  }
}
