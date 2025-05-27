#pragma once
#include "lex.h"

// On all relevant targets (amd64, aarch64, riscv), syscalls take up to 6
// register arguments.
static const u64 max_syscall_args_count = 6;

typedef enum : u8 {
  AST_NODE_KIND_NONE,
  AST_NODE_KIND_NUMBER,
  AST_NODE_KIND_IDENTIFIER,
  AST_NODE_KIND_ADD,
  AST_NODE_KIND_BLOCK,
  AST_NODE_KIND_VAR_DEFINITION,
  AST_NODE_KIND_ADDRESS_OF,
  AST_NODE_KIND_BRANCH,
  AST_NODE_KIND_JUMP,
  AST_NODE_KIND_COMPARISON,
  AST_NODE_KIND_BUILTIN_ASSERT,
  AST_NODE_KIND_SYSCALL,
  AST_NODE_KIND_FN_DEFINITION,
  AST_NODE_KIND_LABEL_DEFINITION,
  AST_NODE_KIND_LABEL,
  AST_NODE_KIND_BUILTIN_TRAP,
} AstNodeKind;

typedef enum [[clang::flag_enum]] : u8 {
  AST_NODE_FLAG_NONE = 0,
  AST_NODE_FLAG_GLOBAL = 1 << 0,
  AST_NODE_FLAG_FN_NO_FRAME_POINTERS = 1 << 1,
} AstNodeFlag;

// Unresolved.
typedef struct {
  PgString value;
} Label;

typedef struct {
  Origin origin;
  union {
    u64 n64;              // Number literal.
    PgString s;           // Variable name.
    u32 stack_args_count; // Function, syscall, etc.
    Label label;
  } u;
  LexTokenKind token_kind;
  AstNodeFlag flags;
  AstNodeKind kind;
} AstNode;
PG_DYN(AstNode) AstNodeDyn;

typedef struct {
  u32 value;
} AstNodeIndex;
PG_DYN(AstNodeIndex) AstNodeIndexDyn;

typedef struct {
  Lexer lexer;
  u64 tokens_consumed;
  ErrorDyn *errors;
  AstNodeDyn nodes;

  // Gets incremented.
  u32 label_id;

  bool err_mode;
} AstParser;

typedef struct {
  u32 value;
} MetadataIndex;
PG_DYN(MetadataIndex) MetadataIndexDyn;

static void ast_advance_to_next_line_from_last_error(AstParser *parser) {
  // Already at EOF.
  if (parser->tokens_consumed >= parser->lexer.tokens.len) {
    return;
  }

  PG_ASSERT(parser->errors->len);
  Error last_err = PG_SLICE_LAST(*parser->errors);
  u32 line =
      PG_SLICE_AT(parser->lexer.tokens, parser->tokens_consumed).origin.line;
  if (line > last_err.origin.line) {
    return;
  }

  for (; parser->tokens_consumed < parser->lexer.tokens.len;
       parser->tokens_consumed++) {
    LexToken token = PG_SLICE_AT(parser->lexer.tokens, parser->tokens_consumed);
    if (token.origin.line > line) {
      break;
    }
  }
}

static void ast_add_error(AstParser *parser, ErrorKind error_kind,
                          Origin origin, PgAllocator *allocator) {
  if (parser->err_mode) {
    return;
  }
  parser->err_mode = true;

  PG_ASSERT(origin.line);

  *PG_DYN_PUSH(parser->errors, allocator) = (Error){
      .kind = error_kind,
      .origin = origin,
      .src = parser->lexer.src,
      // FIXME
      .src_span = PG_SLICE_RANGE(parser->lexer.src, origin.file_offset_start,
                                 origin.file_offset_start + 1),
  };

  // Skip to the next newline to avoid having cascading errors.
  ast_advance_to_next_line_from_last_error(parser);
}

// Best effort to find the closest token when doing error reporting.
[[nodiscard]]
static LexToken ast_current_or_last_token(AstParser parser) {
  LexToken res = {0};

  if (parser.tokens_consumed >= parser.lexer.tokens.len) {
    return PG_DYN_LAST(parser.lexer.tokens);
  }

  res = PG_SLICE_AT(parser.lexer.tokens, parser.tokens_consumed);
  PG_ASSERT(res.kind);
  if (LEX_TOKEN_KIND_EOF != res.kind) {
    return res;
  }

  PG_ASSERT(parser.tokens_consumed > 0);
  return PG_SLICE_AT(parser.lexer.tokens, parser.tokens_consumed - 1);
}

static void ast_push(AstParser *parser, AstNode node, PgAllocator *allocator) {
  *PG_DYN_PUSH(&parser->nodes, allocator) = node;
}

static void ast_print_node(AstNode node) {
  origin_print(node.origin);
  putchar(' ');

  switch (node.kind) {
  case AST_NODE_KIND_NUMBER:
    printf("U64 %" PRIu64, node.u.n64);
    break;
  case AST_NODE_KIND_IDENTIFIER:
    printf("Identifier %.*s", (i32)node.u.s.len, node.u.s.data);
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
    PG_ASSERT(node.u.stack_args_count > 0);
    PG_ASSERT(node.u.stack_args_count <= max_syscall_args_count);
    printf("Syscall(%u)", node.u.stack_args_count);
  } break;
  case AST_NODE_KIND_BLOCK: {
    printf("Block");
  } break;
  case AST_NODE_KIND_VAR_DEFINITION:
    printf("VarDef %.*s", (i32)node.u.s.len, node.u.s.data);
    break;
  case AST_NODE_KIND_BRANCH:
    printf("Branch");
    break;
  case AST_NODE_KIND_JUMP:
    printf("Jump");
    break;
  case AST_NODE_KIND_FN_DEFINITION:
    printf("FnDefinition %.*s", (i32)node.u.s.len, node.u.s.data);
    break;
  case AST_NODE_KIND_LABEL_DEFINITION:
    printf("LabelDefinition %.*s", (i32)node.u.label.value.len,
           node.u.label.value.data);
    break;
  case AST_NODE_KIND_LABEL:
    printf("Label %.*s", (i32)node.u.label.value.len, node.u.label.value.data);
    break;
  case AST_NODE_KIND_BUILTIN_TRAP:
    printf("Trap");
    break;
  case AST_NODE_KIND_NONE:
  default:
    PG_ASSERT(0);
  }
}

static void ast_print_nodes(AstNodeDyn nodes) {
  for (u32 i = 0; i < nodes.len; i++) {
    printf("[%u] ", i);
    AstNode node = PG_SLICE_AT(nodes, i);
    ast_print_node(node);
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
  if (parser->err_mode) {
    return false;
  }

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
                  token_colon_equal.origin, allocator);
    return false;
  }

  AstNode node = {0};
  node.kind = AST_NODE_KIND_VAR_DEFINITION;
  node.origin = token_first.origin;
  node.u.s = token_first.s;
  ast_push(parser, node, allocator);

  return true;
}

[[nodiscard]]
static bool ast_parse_primary(AstParser *parser, PgAllocator *allocator) {
  if (parser->err_mode) {
    return false;
  }

  LexToken first = ast_match_token_kind1_or_kind2(
      parser, LEX_TOKEN_KIND_LITERAL_NUMBER, LEX_TOKEN_KIND_IDENTIFIER);

  if (LEX_TOKEN_KIND_LITERAL_NUMBER == first.kind) {
    AstNode node = {0};
    node.kind = AST_NODE_KIND_NUMBER;
    node.origin = first.origin;
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
    node.u.s = first.s;
    ast_push(parser, node, allocator);

    return true;
  }

  return false;
}

[[nodiscard]]
static bool ast_parse_call(AstParser *parser, PgAllocator *allocator) {
  if (parser->err_mode) {
    return false;
  }

  return ast_parse_primary(parser, allocator);
}

[[nodiscard]] static bool ast_node_is_addressable(AstNode node) {
  // TODO: Expand.
  return AST_NODE_KIND_IDENTIFIER == node.kind;
}

[[nodiscard]]
static bool ast_parse_unary(AstParser *parser, PgAllocator *allocator) {
  if (parser->err_mode) {
    return false;
  }

  LexToken token_first = ast_match_token_kind(parser, LEX_TOKEN_KIND_AMPERSAND);
  if (!token_first.kind) {
    return ast_parse_call(parser, allocator);
  }

  if (!ast_parse_unary(parser, allocator)) {
    ast_add_error(parser, ERROR_KIND_PARSE_UNARY_MISSING_RHS,
                  ast_current_or_last_token(*parser).origin, allocator);
    return false;
  }

  if (!ast_node_is_addressable(PG_SLICE_LAST(parser->nodes))) {
    ast_add_error(parser, ERROR_KIND_ADDRESS_OF_RHS_NOT_ADDRESSABLE,
                  token_first.origin, allocator);
    return false;
  }

  AstNode node = {0};
  node.kind = AST_NODE_KIND_ADDRESS_OF;
  node.origin = token_first.origin;
  ast_push(parser, node, allocator);

  return true;
}

[[nodiscard]]
static bool ast_parse_factor(AstParser *parser, PgAllocator *allocator) {
  if (parser->err_mode) {
    return false;
  }

  return ast_parse_unary(parser, allocator);
}

[[nodiscard]]
static bool ast_parse_term(AstParser *parser, PgAllocator *allocator) {
  if (parser->err_mode) {
    return false;
  }

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
    node.kind = AST_NODE_KIND_ADD;
    node.origin = token.origin;
    ast_push(parser, node, allocator);
  }
  return ast_match_token_kind(parser, LEX_TOKEN_KIND_EOF).kind !=
         LEX_TOKEN_KIND_NONE;
}

[[nodiscard]]
static bool ast_parse_comparison(AstParser *parser, PgAllocator *allocator) {
  if (parser->err_mode) {
    return false;
  }

  return ast_parse_term(parser, allocator);
}

[[nodiscard]]
static bool ast_parse_equality(AstParser *parser, PgAllocator *allocator) {
  if (parser->err_mode) {
    return false;
  }

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
    node.kind = AST_NODE_KIND_COMPARISON;
    node.origin = token.origin;
    node.token_kind = token.kind;
    ast_push(parser, node, allocator);
  }
  return ast_match_token_kind(parser, LEX_TOKEN_KIND_EOF).kind !=
         LEX_TOKEN_KIND_NONE;
}

[[nodiscard]]
static bool ast_parse_logic_and(AstParser *parser, PgAllocator *allocator) {
  if (parser->err_mode) {
    return false;
  }

  return ast_parse_equality(parser, allocator);
}

[[nodiscard]]
static bool ast_parse_logic_or(AstParser *parser, PgAllocator *allocator) {
  if (parser->err_mode) {
    return false;
  }

  return ast_parse_logic_and(parser, allocator);
}

[[nodiscard]]
static bool ast_parse_assignment(AstParser *parser, PgAllocator *allocator) {
  if (parser->err_mode) {
    return false;
  }

  return ast_parse_logic_or(parser, allocator);
}

[[nodiscard]]
static bool ast_parse_expr(AstParser *parser, PgAllocator *allocator) {
  if (parser->err_mode) {
    return false;
  }

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
  if (parser->err_mode) {
    return false;
  }

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
  node.kind = AST_NODE_KIND_SYSCALL;
  node.origin = token_first.origin;
  node.u.stack_args_count = args_count;
  ast_push(parser, node, allocator);

  return true;
}

[[nodiscard]]
static bool ast_parse_block(AstParser *parser, PgAllocator *allocator) {
  if (parser->err_mode) {
    return false;
  }

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
      node.kind = AST_NODE_KIND_BLOCK;
      node.origin = token_first.origin;
      node.u.stack_args_count = args_count;
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
  if (parser->err_mode) {
    return false;
  }

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

  PgString label_prefix = pg_string_concat(
      PG_S(".if-"), pg_u64_to_string(++parser->label_id, allocator), allocator);
  Label branch_then_label = {
      pg_string_concat(label_prefix, PG_S("-then"), allocator)};
  Label branch_else_label = {
      pg_string_concat(label_prefix, PG_S("-else"), allocator)};
  Label branch_end_label = {
      pg_string_concat(label_prefix, PG_S("-end"), allocator)};

  {
    AstNode jump_if_then_label = {0};
    jump_if_then_label.kind = AST_NODE_KIND_LABEL;
    jump_if_then_label.origin = ast_current_or_last_token(*parser).origin;
    jump_if_then_label.u.label = branch_then_label;
    ast_push(parser, jump_if_then_label, allocator);

    AstNode jump_else_label = {0};
    jump_else_label.kind = AST_NODE_KIND_LABEL;
    jump_else_label.origin = ast_current_or_last_token(*parser).origin;
    jump_else_label.u.label = branch_else_label;
    ast_push(parser, jump_else_label, allocator);

    AstNode jump_end_label = {0};
    jump_end_label.kind = AST_NODE_KIND_LABEL;
    jump_end_label.origin = ast_current_or_last_token(*parser).origin;
    jump_end_label.u.label = branch_end_label;
    ast_push(parser, jump_end_label, allocator);

    AstNode branch = {0};
    branch.kind = AST_NODE_KIND_BRANCH;
    branch.origin = token_first.origin;
    ast_push(parser, branch, allocator);

    // Not absolutely needed but makes AST more readable and useful later for
    // the CFG.
    AstNode jump_if_then_label_def = {0};
    jump_if_then_label_def.kind = AST_NODE_KIND_LABEL_DEFINITION;
    jump_if_then_label_def.origin = token_first.origin;
    jump_if_then_label_def.u.label = branch_then_label;
    ast_push(parser, jump_if_then_label_def, allocator);
  }

  if (!ast_parse_block(parser, allocator)) {
    ast_add_error(parser, ERROR_KIND_PARSE_IF_MISSING_THEN_BLOCK,
                  token_first.origin, allocator);
    return false;
  }

  {
    AstNode jump_if_end_label = {0};
    jump_if_end_label.kind = AST_NODE_KIND_LABEL;
    jump_if_end_label.origin = token_first.origin;
    jump_if_end_label.u.label = branch_end_label;
    ast_push(parser, jump_if_end_label, allocator);

    AstNode jump = {0};
    jump.kind = AST_NODE_KIND_JUMP;
    jump.origin = token_first.origin;
    jump.u.label = branch_then_label;
    ast_push(parser, jump, allocator);
  }

  AstNode jump_else_label_def = {0};
  jump_else_label_def.kind = AST_NODE_KIND_LABEL_DEFINITION;
  jump_else_label_def.origin = token_first.origin;
  jump_else_label_def.u.label = branch_else_label;
  ast_push(parser, jump_else_label_def, allocator);

  // TODO: optional else.

  AstNode jump_if_end_label_def = {0};
  jump_if_end_label_def.kind = AST_NODE_KIND_LABEL_DEFINITION;
  jump_if_end_label_def.origin = token_first.origin;
  jump_if_end_label_def.u.label = branch_end_label;
  ast_push(parser, jump_if_end_label_def, allocator);

  return true;
}

[[nodiscard]]
static bool ast_parse_statement_assert(AstParser *parser,
                                       PgAllocator *allocator) {
  if (parser->err_mode) {
    return false;
  }

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
  node.kind = AST_NODE_KIND_BUILTIN_ASSERT;
  node.origin = token_first.origin;
  ast_push(parser, node, allocator);

  return true;
}

[[nodiscard]]
static bool ast_parse_statement(AstParser *parser, PgAllocator *allocator) {
  if (parser->err_mode) {
    return false;
  }

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
  if (parser->err_mode) {
    return false;
  }

  if (ast_parse_var_decl(parser, allocator)) {
    return true;
  }

  return ast_parse_statement(parser, allocator);
}

static void ast_emit_program_epilog(AstParser *parser, PgAllocator *allocator) {
  {
    AstNode fn = {0};
    fn.kind = AST_NODE_KIND_FN_DEFINITION;
    fn.u.s = PG_S("__builtin_exit");
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
    syscall.u.stack_args_count = 2;
    ast_push(parser, syscall, allocator);
  }
}

static void ast_emit(AstParser *parser, PgAllocator *allocator) {
  AstNode fn_start = {0};
  fn_start.kind = AST_NODE_KIND_FN_DEFINITION;
  fn_start.u.s = PG_S("_start");
  fn_start.flags = AST_NODE_FLAG_GLOBAL;
  // TODO: Do not define this function to avoid recursive calls to it.
  ast_push(parser, fn_start, allocator);

  for (u64 _i = 0; _i < parser->lexer.tokens.len;) {
    // End.
    if (parser->tokens_consumed >= parser->lexer.tokens.len) {
      break;
    }

    if (parser->err_mode) {
      ast_advance_to_next_line_from_last_error(parser);
      parser->err_mode = false;
    }

    if (ast_match_token_kind(parser, LEX_TOKEN_KIND_EOF).kind) {
      break;
    }

    if (!ast_parse_declaration(parser, allocator)) {
      continue;
    }
  }

  ast_emit_program_epilog(parser, allocator);
}

static void ast_constant_fold(AstNodeDyn nodes_before, AstNodeDyn *nodes_after,
                              PgAllocator *allocator) {

  AstNodeDyn stack = {0};
  PG_DYN_ENSURE_CAP(&stack, 512, allocator);

  for (u32 i = 0; i < nodes_before.len; i++) {
    AstNode node = PG_SLICE_AT(nodes_before, i);

    switch (node.kind) {
    case AST_NODE_KIND_LABEL:
    case AST_NODE_KIND_LABEL_DEFINITION:
    case AST_NODE_KIND_IDENTIFIER:
    case AST_NODE_KIND_NUMBER: {
      *PG_DYN_PUSH(&stack, allocator) = node;
    } break;

    case AST_NODE_KIND_ADD: {
      AstNode rhs = PG_DYN_POP(&stack);
      AstNode lhs = PG_DYN_POP(&stack);

      if (AST_NODE_KIND_NUMBER == lhs.kind &&
          AST_NODE_KIND_NUMBER == rhs.kind) {
        AstNode folded = lhs;
        folded.u.n64 += rhs.u.n64;

        PG_DYN_POP(nodes_after);
        PG_DYN_POP(nodes_after);

        *PG_DYN_PUSH_WITHIN_CAPACITY(nodes_after) = folded;
        *PG_DYN_PUSH(&stack, allocator) = folded;
        continue;
      }
      *PG_DYN_PUSH(&stack, allocator) = node;
    } break;

    case AST_NODE_KIND_COMPARISON: {
      AstNode rhs = PG_DYN_POP(&stack);
      AstNode lhs = PG_DYN_POP(&stack);

      if (AST_NODE_KIND_NUMBER == lhs.kind &&
          AST_NODE_KIND_NUMBER == rhs.kind) {
        AstNode folded = lhs;
        folded.u.n64 = lhs.u.n64 == rhs.u.n64;

        PG_DYN_POP(nodes_after);
        PG_DYN_POP(nodes_after);

        *PG_DYN_PUSH_WITHIN_CAPACITY(nodes_after) = folded;
        *PG_DYN_PUSH(&stack, allocator) = folded;
        continue;
      }
      *PG_DYN_PUSH(&stack, allocator) = node;
    } break;

    case AST_NODE_KIND_FN_DEFINITION: {
      stack.len = 0;
    } break;

    case AST_NODE_KIND_JUMP:
    case AST_NODE_KIND_BUILTIN_ASSERT:
    case AST_NODE_KIND_VAR_DEFINITION: {
      PG_DYN_POP(&stack);
    } break;

    case AST_NODE_KIND_ADDRESS_OF: {
      PG_DYN_POP(&stack);
      *PG_DYN_PUSH(&stack, allocator) = node;
    } break;

    case AST_NODE_KIND_BRANCH: {
      PG_DYN_POP(&stack);
      PG_DYN_POP(&stack);
      PG_DYN_POP(&stack);
    } break;

    case AST_NODE_KIND_BLOCK:
    case AST_NODE_KIND_SYSCALL: {
      for (u64 k = 0; k < node.u.stack_args_count; k++) {
        PG_DYN_POP(&stack);
      }
    } break;

    case AST_NODE_KIND_BUILTIN_TRAP:
      break;

    case AST_NODE_KIND_NONE:
    default:
      PG_ASSERT(0);
    }
    *PG_DYN_PUSH(nodes_after, allocator) = node;
  }
}
