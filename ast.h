#pragma once
#include "amd64.h"
#include "submodules/cstd/lib.c"

/* typedef struct { */
/*   u32 value; */
/* } AstNodeIndex; */
/* PG_SLICE(AstNodeIndex) AstNodeIndexSlice; */

typedef enum {
  AST_NODE_KIND_NONE,
  AST_NODE_KIND_U64,
  AST_NODE_KIND_ADD,
  AST_NODE_KIND_SYSCALL,
} AstNodeKind;

typedef struct AstNode {
  AstNodeKind kind;
  struct AstNode *operand1, *operand2;
  u64 n64;
} AstNode;

static void ast_to_asm_instructions(AstNode *root,
                                    Amd64InstructionDyn *instructions,
                                    Amd64ConstantDyn *constants,
                                    PgAllocator *allocator) {
  switch (root->kind) {
  case AST_NODE_KIND_NONE:
    PG_ASSERT(0);
  case AST_NODE_KIND_U64:
  case AST_NODE_KIND_ADD:
  case AST_NODE_KIND_SYSCALL:
    break;
  default:
    PG_ASSERT(0);
  }
}

[[nodiscard]] static Amd64Program ast_to_asm(AstNode *root, PgString file_name,
                                             u64 vm_start,
                                             PgAllocator *allocator) {
  u64 rodata_offset = 0x2000;

  Amd64Constant constant_hello_world = {
      .name = PG_S("hello_world"),
      .kind = AMD64_CONSTANT_KIND_BYTES,
      .bytes = PG_S("Hello, world!"),
      // TODO: Should it be backpatched?
      .address_absolute = vm_start + rodata_offset + 0x00,
  };
  Amd64ConstantDyn constants = {0};
  PG_DYN_ENSURE_CAP(&constants, 256, allocator);
  *PG_DYN_PUSH(&constants, allocator) = constant_hello_world;

  Amd64InstructionDyn instructions = {0};
  PG_DYN_ENSURE_CAP(&instructions, 512, allocator);

  Amd64SectionDyn sections = {0};
  PG_DYN_ENSURE_CAP(&sections, 32, allocator);

  Amd64Section section_start = {
      .name = PG_S("_start"),
      .flags = AMD64_SECTION_FLAG_GLOBAL,
      .instructions = PG_DYN_SLICE(Amd64InstructionSlice, instructions),
  };
  *PG_DYN_PUSH(&sections, allocator) = section_start;

  ast_to_asm_instructions(root, &instructions, &constants, allocator);

  Amd64Program program = {
      .file_name = file_name,
      .vm_start = vm_start,
      .text = PG_DYN_SLICE(Amd64SectionSlice, sections),
      .rodata = PG_DYN_SLICE(Amd64ConstantSlice, constants),
  };

  return program;
}
