#pragma once
#include "ast.h"

typedef enum : u8 {
  IR_INSTRUCTION_KIND_NONE,
  IR_INSTRUCTION_KIND_IDENTIFIER,
  IR_INSTRUCTION_KIND_ADD,
  IR_INSTRUCTION_KIND_MOV,
  IR_INSTRUCTION_KIND_LOAD_ADDRESS,
  IR_INSTRUCTION_KIND_JUMP_IF_FALSE,
  IR_INSTRUCTION_KIND_JUMP,
  IR_INSTRUCTION_KIND_COMPARISON,
  IR_INSTRUCTION_KIND_SYSCALL,
  IR_INSTRUCTION_KIND_FN_DEFINITION,
  IR_INSTRUCTION_KIND_LABEL_DEFINITION,
  IR_INSTRUCTION_KIND_TRAP,
} IrInstructionKind;

#define IR_FLAG_GLOBAL (1 << 0)

typedef enum {
  IR_OPERAND_KIND_NONE,
  IR_OPERAND_KIND_NUM,
  IR_OPERAND_KIND_LABEL,
  IR_OPERAND_KIND_VREG,
  IR_OPERAND_KIND_STRING,
} IrOperandKind;

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
  IrOperandKind kind;

  union {
    Label label;
    VirtualRegister vreg;
    u64 u64;
    PgString s;
  } u;
} IrOperand;

typedef struct {
  u32 value;
} MetadataIndex;

typedef struct {
  u32 value;
} InstructionIndex;

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
PG_DYN(MemoryLocation) MemoryLocationDyn;

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
  IrInstructionKind kind;
  u16 flags;
  Origin origin;
  MetadataIndex meta_idx;
  IrOperand lhs, rhs;
  u64 extra_data;
} IrInstruction;
PG_DYN(IrInstruction) IrInstructionDyn;

typedef struct {
  u32 label_id;
} IrEmitter;

// Graph represented as a adjacency matrix (M(i,j) = 1 if there is an edge
// between i and j), stored as a bitfield of the right-upper half (without the
// diagonal).
// Each row is a memory location (see above field).
typedef PgAdjacencyMatrix InterferenceGraph;

typedef struct {
  PgString name;
  MetadataDyn metadata;
  IrInstructionDyn instructions;

  u32 stack_base_pointer_offset;
  u32 stack_base_pointer_offset_max;

  InterferenceGraph interference_graph;
} FnDefinition;
PG_DYN(FnDefinition) FnDefinitionDyn;

[[nodiscard]] static MetadataIndex metadata_last_idx(MetadataDyn metadata) {
  PG_ASSERT(metadata.len > 0);
  return (MetadataIndex){(u32)metadata.len - 1};
}

[[maybe_unused]] [[nodiscard]]
static MetadataIndex metadata_make(MetadataDyn *metadata,
                                   PgAllocator *allocator) {
  Metadata res = {0};
  res.virtual_register.value = (u32)metadata->len;

  *PG_DYN_PUSH(metadata, allocator) = res;

  return metadata_last_idx(*metadata);
}

[[maybe_unused]]
static void metadata_start_lifetime(MetadataDyn metadata,
                                    MetadataIndex meta_idx,
                                    InstructionIndex ins_idx) {
  PG_SLICE_AT(metadata, meta_idx.value).lifetime_start = ins_idx;
  PG_SLICE_AT(metadata, meta_idx.value).lifetime_end = ins_idx;
}

// TODO: Scopes.
// TODO: Detect shadowing.
// TODO: LUT to cache result.
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

[[maybe_unused]]
static void metadata_extend_lifetime_on_use(MetadataDyn metadata,
                                            IrInstruction ins,
                                            InstructionIndex ins_idx) {
  PG_SLICE_AT(metadata, ins.meta_idx.value).lifetime_end = ins_idx;

  // TODO: Variable pointed to needs to live at least as long as the pointer to
  // it.
  // TODO: If there are multiple aliases to the same pointer, all aliases
  // should have their meta extended to this point!
  // TODO: Dataflow.

  if (IR_INSTRUCTION_KIND_IDENTIFIER == ins.kind) {
    PgString s = PG_S("FIXME");
    Metadata *meta = metadata_find_by_identifier(metadata, s);
    PG_ASSERT(meta);
    meta->lifetime_end = ins_idx;
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

static void ir_print_operand(IrOperand operand) {
  switch (operand.kind) {
  case IR_OPERAND_KIND_NUM:
    printf("%lu", operand.u.u64);
    break;

  case IR_OPERAND_KIND_STRING:
    PG_ASSERT(operand.u.s.len);
    printf("%.*s", (i32)operand.u.s.len, operand.u.s.data);
    break;

  case IR_OPERAND_KIND_LABEL:
    PG_ASSERT(operand.u.label.value.len);
    printf("%.*s", (i32)operand.u.label.value.len, operand.u.label.value.data);
    break;

  case IR_OPERAND_KIND_VREG:
    PG_ASSERT(operand.u.vreg.value);
    printf("v%u", operand.u.vreg.value);
    break;

  case IR_OPERAND_KIND_NONE:
  default:
    PG_ASSERT(0);
  }
}

static void ir_print_instructions(IrInstructionDyn instructions) {
  for (u32 i = 0; i < instructions.len; i++) {
    printf("[%u] ", i);
    IrInstruction ins = PG_SLICE_AT(instructions, i);
    origin_print(ins.origin);
    printf(": ");

    switch (ins.kind) {
    case IR_INSTRUCTION_KIND_IDENTIFIER:
      PG_ASSERT(IR_OPERAND_KIND_STRING == ins.lhs.kind);
      PG_ASSERT(IR_OPERAND_KIND_NONE == ins.rhs.kind);

      printf("Identifier ");
      ir_print_operand(ins.lhs);
      break;

    case IR_INSTRUCTION_KIND_ADD:
      PG_ASSERT(IR_OPERAND_KIND_NUM == ins.lhs.kind ||
                IR_OPERAND_KIND_VREG == ins.lhs.kind);
      PG_ASSERT(IR_OPERAND_KIND_NUM == ins.rhs.kind ||
                IR_OPERAND_KIND_VREG == ins.rhs.kind);

      printf("Add v%u, ", i);
      ir_print_operand(ins.lhs);
      printf(", ");
      ir_print_operand(ins.rhs);
      break;

    case IR_INSTRUCTION_KIND_COMPARISON:
      PG_ASSERT(IR_OPERAND_KIND_NUM == ins.lhs.kind ||
                IR_OPERAND_KIND_VREG == ins.lhs.kind);
      PG_ASSERT(IR_OPERAND_KIND_NUM == ins.rhs.kind ||
                IR_OPERAND_KIND_VREG == ins.rhs.kind);

      printf("Cmp v%u, ", i);
      ir_print_operand(ins.lhs);
      printf(", ");
      ir_print_operand(ins.rhs);
      break;

    case IR_INSTRUCTION_KIND_MOV:
      PG_ASSERT(IR_OPERAND_KIND_NUM == ins.lhs.kind ||
                IR_OPERAND_KIND_VREG == ins.lhs.kind);
      PG_ASSERT(IR_OPERAND_KIND_NONE == ins.rhs.kind);

      printf("Mov v%u, ", i);
      ir_print_operand(ins.lhs);
      break;

    case IR_INSTRUCTION_KIND_LOAD_ADDRESS:
      PG_ASSERT(IR_OPERAND_KIND_VREG == ins.lhs.kind);
      PG_ASSERT(IR_OPERAND_KIND_NONE == ins.rhs.kind);

      printf("LoadAddr v%u, ", i);
      ir_print_operand(ins.lhs);
      break;

    case IR_INSTRUCTION_KIND_JUMP_IF_FALSE:
      PG_ASSERT(ins.extra_data);
      PG_ASSERT(IR_OPERAND_KIND_LABEL == ins.lhs.kind);
      PG_ASSERT(IR_OPERAND_KIND_LABEL == ins.rhs.kind);

      printf("JumpIfFalse v%lu, ", ins.extra_data);
      ir_print_operand(ins.lhs);
      printf(", ");
      ir_print_operand(ins.rhs);
      break;

    case IR_INSTRUCTION_KIND_JUMP:
      PG_ASSERT(IR_OPERAND_KIND_LABEL == ins.lhs.kind);
      PG_ASSERT(IR_OPERAND_KIND_NONE == ins.rhs.kind);

      printf("Jump ");
      ir_print_operand(ins.lhs);
      break;

    case IR_INSTRUCTION_KIND_SYSCALL:
      PG_ASSERT(IR_OPERAND_KIND_NONE == ins.lhs.kind);
      PG_ASSERT(IR_OPERAND_KIND_NONE == ins.rhs.kind);
      PG_ASSERT(ins.extra_data > 0);
      PG_ASSERT(ins.extra_data <= max_syscall_args_count);

      printf("Syscall");
      break;

    case IR_INSTRUCTION_KIND_FN_DEFINITION:
      PG_ASSERT(IR_OPERAND_KIND_STRING == ins.lhs.kind);
      PG_ASSERT(IR_OPERAND_KIND_NONE == ins.rhs.kind);

      printf("FnDef ");
      ir_print_operand(ins.lhs);
      break;
    case IR_INSTRUCTION_KIND_LABEL_DEFINITION:
      PG_ASSERT(IR_OPERAND_KIND_LABEL == ins.lhs.kind);
      PG_ASSERT(IR_OPERAND_KIND_NONE == ins.rhs.kind);

      printf("Label ");
      ir_print_operand(ins.lhs);
      break;
    case IR_INSTRUCTION_KIND_TRAP:
      PG_ASSERT(IR_OPERAND_KIND_NONE == ins.lhs.kind);
      PG_ASSERT(IR_OPERAND_KIND_NONE == ins.rhs.kind);

      printf("Trap");
      break;

    case IR_INSTRUCTION_KIND_NONE:
    default:
      break;
    }
    printf("\n");
  }
}

static void ir_print_fn_def(FnDefinition fn_def) {
  PG_ASSERT(fn_def.name.len);

  printf("%.*s:\n", (i32)fn_def.name.len, fn_def.name.data);

  ir_print_instructions(fn_def.instructions);

  printf("\n");
}

static void ir_print_fn_defs(FnDefinitionDyn fn_defs) {
  for (u32 i = 0; i < fn_defs.len; i++) {
    FnDefinition fn_def = PG_SLICE_AT(fn_defs, i);
    ir_print_fn_def(fn_def);
  }
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

[[maybe_unused]]
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

[[nodiscard]] static IrOperand ir_make_synth_label(u32 *label_current,
                                                   PgAllocator *allocator) {
  IrOperand res = {0};
  res.kind = IR_OPERAND_KIND_LABEL;
  res.u.label.value = pg_string_concat(
      PG_S("."), pg_u64_to_string(++(*label_current), allocator), allocator);
  return res;
}

[[nodiscard]] static IrInstructionDyn
ir_emit_from_ast(IrEmitter *emitter, AstNodeDyn nodes, PgAllocator *allocator) {
  (void)emitter; // FIXME

  IrInstructionDyn res = {0};
  PG_DYN_ENSURE_CAP(&res, nodes.len * 2, allocator);

  AstNodeDyn stack = {0};
  PG_DYN_ENSURE_CAP(&stack, 512, allocator);

  for (u32 i = 0; i < nodes.len; i++) {
    AstNode node = PG_SLICE_AT(nodes, i);

    switch (node.kind) {
    case AST_NODE_KIND_NUMBER: {
      IrInstruction ins = {0};
      ins.kind = IR_INSTRUCTION_KIND_MOV;
      ins.origin = node.origin;
      ins.lhs = (IrOperand){
          .kind = IR_OPERAND_KIND_NUM,
          .u.u64 = node.u.n64,
      };
      *PG_DYN_PUSH(&res, allocator) = ins;
    } break;

    case AST_NODE_KIND_IDENTIFIER: {
      IrInstruction ins = {0};
      ins.kind = IR_INSTRUCTION_KIND_IDENTIFIER;
      ins.origin = node.origin;
      ins.lhs = (IrOperand){.kind = IR_OPERAND_KIND_STRING, .u.s = node.u.s};
      *PG_DYN_PUSH(&res, allocator) = ins;
    } break;

    case AST_NODE_KIND_ADD: {
      IrInstruction ins = {0};
      ins.kind = IR_INSTRUCTION_KIND_ADD;
      ins.origin = node.origin;
      PG_ASSERT(res.len >= 2);
      ins.lhs = (IrOperand){
          .kind = IR_OPERAND_KIND_VREG,
          .u.vreg.value = (u32)res.len - 2,
      };
      ins.rhs = (IrOperand){
          .kind = IR_OPERAND_KIND_VREG,
          .u.vreg.value = (u32)res.len - 1,
      };

      *PG_DYN_PUSH(&res, allocator) = ins;
    } break;

    case AST_NODE_KIND_COMPARISON: {
      IrInstruction ins = {0};
      ins.kind = IR_INSTRUCTION_KIND_COMPARISON;
      ins.origin = node.origin;
      PG_ASSERT(res.len >= 2);
      ins.lhs = (IrOperand){
          .kind = IR_OPERAND_KIND_VREG,
          .u.vreg.value = (u32)res.len - 2,
      };
      ins.rhs = (IrOperand){
          .kind = IR_OPERAND_KIND_VREG,
          .u.vreg.value = (u32)res.len - 1,
      };

      *PG_DYN_PUSH(&res, allocator) = ins;
    } break;

    case AST_NODE_KIND_BLOCK: {
      PG_ASSERT(0 && "todo");
    } break;

    case AST_NODE_KIND_VAR_DEFINITION: {
      PG_ASSERT(res.len > 0);

      IrInstruction ins = {0};
      ins.kind = IR_INSTRUCTION_KIND_MOV;
      ins.origin = node.origin;
      ins.lhs = (IrOperand){
          .kind = IR_OPERAND_KIND_VREG,
          .u.vreg.value = (u32)res.len - 1,
      };
      // Remember the node index to access the identifier during resolving.
      ins.extra_data = i;
      *PG_DYN_PUSH(&res, allocator) = ins;
    } break;

    case AST_NODE_KIND_ADDRESS_OF: {
      PG_ASSERT(res.len >= 1);

      IrInstruction ins = {0};
      ins.kind = IR_INSTRUCTION_KIND_LOAD_ADDRESS;
      ins.origin = node.origin;
      ins.rhs = (IrOperand){
          .kind = IR_OPERAND_KIND_VREG,
          .u.vreg.value = (u32)res.len - 1,
      };
      *PG_DYN_PUSH(&res, allocator) = ins;
    } break;

    case AST_NODE_KIND_BRANCH: {
      PG_ASSERT(res.len >= 1);

      IrInstruction ins = {0};
      ins.kind = IR_INSTRUCTION_KIND_JUMP_IF_FALSE;
      ins.origin = node.origin;
      PG_ASSERT(0 && "todo");
    } break;

    case AST_NODE_KIND_JUMP: {
      PG_ASSERT(res.len > 0);

      AstNode op = PG_SLICE_AT(nodes, i - 1);
      PG_ASSERT(AST_NODE_KIND_LABEL == op.kind);

      IrInstruction ins = {0};
      ins.kind = IR_INSTRUCTION_KIND_JUMP;
      ins.origin = node.origin;
      ins.lhs = (IrOperand){
          .kind = IR_OPERAND_KIND_LABEL,
          .u.label = op.u.label,
      };
      *PG_DYN_PUSH(&res, allocator) = ins;

    } break;

    case AST_NODE_KIND_LABEL:
      break;

    case AST_NODE_KIND_BUILTIN_TRAP: {
      IrInstruction ins = {0};
      ins.kind = IR_INSTRUCTION_KIND_TRAP;
      ins.origin = node.origin;
      *PG_DYN_PUSH(&res, allocator) = ins;
    } break;

    case AST_NODE_KIND_FN_DEFINITION: {
      IrInstruction ins = {0};
      ins.kind = IR_INSTRUCTION_KIND_FN_DEFINITION;
      ins.origin = node.origin;
      ins.lhs = (IrOperand){.kind = IR_OPERAND_KIND_STRING, .u.s = node.u.s};

      if (node.flags & AST_NODE_FLAG_GLOBAL) {
        ins.flags = IR_FLAG_GLOBAL;
      }

      *PG_DYN_PUSH(&res, allocator) = ins;
    } break;

    case AST_NODE_KIND_SYSCALL: {
      PG_ASSERT(node.u.args_count > 0);
      PG_ASSERT(node.u.args_count <= max_syscall_args_count);

      // TODO: Simply set constraint on existing args vregs?
      for (u64 j = 0; j < node.u.args_count; j++) {
        u64 idx = i - node.u.args_count + j;
        PG_ASSERT(idx <= UINT32_MAX);

        AstNode op = PG_SLICE_AT(nodes, idx);
        PG_ASSERT(ast_node_is_expr(op));

        IrInstruction ins = {0};
        ins.kind = IR_INSTRUCTION_KIND_MOV;
        ins.origin = node.origin;
        ins.lhs = (IrOperand){
            .kind = IR_OPERAND_KIND_VREG,
            .u.vreg.value = (u32)idx,
        };
        *PG_DYN_PUSH(&res, allocator) = ins;
      }

      IrInstruction ins = {0};
      ins.kind = IR_INSTRUCTION_KIND_SYSCALL;
      ins.origin = node.origin;
      ins.extra_data = node.u.args_count;

      *PG_DYN_PUSH(&res, allocator) = ins;
    } break;

    case AST_NODE_KIND_LABEL_DEFINITION: {
      IrInstruction ins = {0};
      ins.kind = IR_INSTRUCTION_KIND_LABEL_DEFINITION;
      ins.origin = node.origin;
      ins.lhs = ir_make_synth_label(&emitter->label_id, allocator);

      *PG_DYN_PUSH(&res, allocator) = ins;

    } break;

    case AST_NODE_KIND_BUILTIN_ASSERT: {
      PG_ASSERT(res.len >= 1);

      IrInstruction ins_cmp = {0};
      ins_cmp.kind = IR_INSTRUCTION_KIND_COMPARISON;
      ins_cmp.lhs = (IrOperand){
          .kind = IR_OPERAND_KIND_NUM,
          .u.u64 = 0,
      };
      ins_cmp.rhs = (IrOperand){
          .kind = IR_OPERAND_KIND_VREG,
          .u.vreg.value = (u32)res.len - 1,
      };
      *PG_DYN_PUSH(&res, allocator) = ins_cmp;

      IrInstruction ins_jmp = {0};
      ins_jmp.kind = IR_INSTRUCTION_KIND_JUMP_IF_FALSE;
      ins_jmp.extra_data = res.len - 1;

      IrOperand if_then_target =
          ir_make_synth_label(&emitter->label_id, allocator);
      IrOperand if_end_target =
          ir_make_synth_label(&emitter->label_id, allocator);

      ins_jmp.lhs = if_then_target;
      ins_jmp.rhs = if_end_target;
      *PG_DYN_PUSH(&res, allocator) = ins_jmp;

      IrInstruction ins_if_then_label = {0};
      ins_if_then_label.kind = IR_INSTRUCTION_KIND_LABEL_DEFINITION;
      ins_if_then_label.lhs = if_then_target;
      *PG_DYN_PUSH(&res, allocator) = ins_if_then_label;

      IrInstruction ins_trap = {0};
      ins_trap.kind = IR_INSTRUCTION_KIND_TRAP;
      *PG_DYN_PUSH(&res, allocator) = ins_trap;

      IrInstruction ins_if_end_label = {0};
      ins_if_end_label.kind = IR_INSTRUCTION_KIND_LABEL_DEFINITION;
      ins_if_end_label.lhs = if_end_target;
      *PG_DYN_PUSH(&res, allocator) = ins_if_end_label;
    } break;

    case AST_NODE_KIND_NONE:
    default:
      PG_ASSERT(0);
    }
  }

  return res;
}

[[nodiscard]]
static FnDefinitionDyn ir_generate_fn_defs(IrInstructionDyn instructions,
                                           PgAllocator *allocator) {

  FnDefinitionDyn fn_defs = {0};
  FnDefinition fn_def = {0};
  fn_def.instructions = instructions;

  for (u32 i = 0; i < instructions.len; i++) {
    IrInstruction *ins = PG_SLICE_AT_PTR(&instructions, i);

    switch (ins->kind) {
    case IR_INSTRUCTION_KIND_MOV:
    case IR_INSTRUCTION_KIND_ADD:
    case IR_INSTRUCTION_KIND_LOAD_ADDRESS:
    case IR_INSTRUCTION_KIND_JUMP_IF_FALSE:
      PG_ASSERT(0);

    case IR_INSTRUCTION_KIND_IDENTIFIER: {
      // Here the variable name is resolved.
      // TODO: Scope aware symbol resolution.
      PgString name = PG_S("FIXME");
      Metadata *meta = metadata_find_by_identifier(fn_def.metadata, name);
      if (!meta) {
        PG_ASSERT(0);
#if 0
        ast_add_error(parser, ERROR_KIND_UNDEFINED_VAR, ins->origin, allocator);
        PG_DYN_LAST(*parser->errors).src_span = node->u.s;
#endif
      }
    } break;

    case IR_INSTRUCTION_KIND_FN_DEFINITION: {
      PG_ASSERT(instructions.len);
      PG_ASSERT(instructions.data);

      fn_def.instructions.len =
          (u64)(PG_SLICE_AT_PTR(&instructions, i) - fn_def.instructions.data);
      *PG_DYN_PUSH(&fn_defs, allocator) = fn_def;

      FnDefinition fn_def_new = {.instructions =
                                     PG_SLICE_RANGE_START(instructions, i)};
      // TODO: Still needed?
      *PG_DYN_PUSH(&fn_def_new.metadata, allocator) = (Metadata){0}; // Dummy.

      *PG_DYN_PUSH(&fn_defs, allocator) = fn_def_new;
    } break;

    case IR_INSTRUCTION_KIND_COMPARISON: {
      PG_SLICE_AT(fn_def.metadata, ins->meta_idx.value)
          .virtual_register.constraint = VREG_CONSTRAINT_CONDITION_FLAGS;
    } break;

    case IR_INSTRUCTION_KIND_SYSCALL: {
      PG_SLICE_AT(fn_def.metadata, ins->meta_idx.value)
          .virtual_register.constraint = VREG_CONSTRAINT_SYSCALL_RET;
    } break;

    case IR_INSTRUCTION_KIND_LABEL_DEFINITION:
    case IR_INSTRUCTION_KIND_JUMP:
    case IR_INSTRUCTION_KIND_TRAP:
      break;

    case IR_INSTRUCTION_KIND_NONE:
    default:
      PG_ASSERT(0);
    }
  }

  return fn_defs;
}
