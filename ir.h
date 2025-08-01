#pragma once
#include "ast.h"
#include "type_check.h"

typedef enum : u8 {
  IR_INSTRUCTION_KIND_NONE,
  IR_INSTRUCTION_KIND_ADD,
  IR_INSTRUCTION_KIND_MOV,
  IR_INSTRUCTION_KIND_LOAD_ADDRESS,
  IR_INSTRUCTION_KIND_JUMP_IF_FALSE,
  IR_INSTRUCTION_KIND_JUMP,
  IR_INSTRUCTION_KIND_COMPARISON,
  IR_INSTRUCTION_KIND_SYSCALL,
  IR_INSTRUCTION_KIND_LABEL_DEFINITION,
  IR_INSTRUCTION_KIND_TRAP,
} IrInstructionKind;

#define IR_FLAG_GLOBAL (1 << 0)

typedef enum : uint8_t {
  IR_OPERAND_KIND_NONE,
  IR_OPERAND_KIND_NUM,
  IR_OPERAND_KIND_LABEL,
  IR_OPERAND_KIND_VREG,
} IrOperandKind;

typedef enum : u8 {
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
  // TODO: Remove.
  u32 value;

  VirtualRegisterConstraint constraint;
  bool addressed;
  bool addressable;
  PG_PAD(1);
} VirtualRegister;
PG_DYN_DECL(VirtualRegister);

typedef struct {
  IrOperandKind kind;
  PG_PAD(7); // TODO: Optimize.

  union {
    Label label;
    MetadataIndex vreg_meta_idx;
    u64 u64;
  } u;
} IrOperand;

typedef struct {
  u32 value;
} InstructionIndex;

typedef struct {
  u8 value;
} Register;
PG_SLICE_DECL(Register);
PG_DYN_DECL(Register);

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
PG_DYN_DECL(MemoryLocation);

typedef struct {
  InstructionIndex lifetime_start, lifetime_end;

  // Result of the IR operation.
  VirtualRegister virtual_register;

  MemoryLocation memory_location;

  // Only for troubleshooting.
  // TODO: Remove?
  PgString identifier;

  Type *type;
#if 0
  bool tombstone;
#endif
} Metadata;
PG_DYN_DECL(Metadata);

typedef struct {
  IrOperand lhs, rhs;
  Origin origin;
  IrInstructionKind kind;
  u8 args_count; // For IR readability only.
  u16 flags;
  MetadataIndex meta_idx;
} IrInstruction;
PG_DYN_DECL(IrInstruction);

typedef struct {
  u32 label_id;
  PG_PAD(4);
  PG_DYN(Error) * errors;
  PgString src;
  Type *types;
} IrEmitter;

// Graph represented as a adjacency matrix (M(i,j) = 1 if there is an edge
// between i and j), stored as a bitfield of the right-upper half (without the
// diagonal).
// Each row is a memory location (see above field).
typedef PgAdjacencyMatrix InterferenceGraph;

typedef struct {
  PgString name;
  PG_DYN(Metadata) metadata;
  PG_DYN(IrInstruction) instructions;

  u32 stack_base_pointer_offset;
  u32 stack_base_pointer_offset_max;

  InterferenceGraph interference_graph;
  Origin origin;
  u16 flags;
  PG_PAD(6); // TODO: Optimize.
} FnDefinition;
PG_DYN_DECL(FnDefinition);

typedef struct {
  AstNodeIndex node_idx;
  MetadataIndex meta_idx;
  Type *type;
  u32 scope_depth;
  PG_PAD(4); // TODO: Optimize.
} IrLocalVar;
PG_DYN_DECL(IrLocalVar);

[[nodiscard]] static MetadataIndex metadata_last_idx(PG_DYN(Metadata)
                                                         metadata) {
  PG_ASSERT(metadata.len > 0);
  return (MetadataIndex){(u32)metadata.len - 1};
}

[[nodiscard]]
static MetadataIndex metadata_make(PG_DYN(Metadata) * metadata, Type *type,
                                   PgAllocator *allocator) {
  Metadata res = {0};
  res.virtual_register.value = (u32)metadata->len;
  res.type = type;

  PG_DYN_PUSH(metadata, res, allocator);

  return metadata_last_idx(*metadata);
}

static void metadata_start_lifetime(PG_DYN(Metadata) metadata,
                                    MetadataIndex meta_idx,
                                    InstructionIndex ins_idx) {
  PG_SLICE_AT(metadata, meta_idx.value).lifetime_start = ins_idx;
  PG_SLICE_AT(metadata, meta_idx.value).lifetime_end = ins_idx;
}

static void metadata_extend_lifetime_on_use(PG_DYN(Metadata) metadata,
                                            MetadataIndex meta_idx,
                                            InstructionIndex ins_idx) {
  PG_ASSERT(meta_idx.value);
  PG_SLICE_AT(metadata, meta_idx.value).lifetime_end = ins_idx;

  // TODO: Variable pointed to needs to live at least as long as the pointer to
  // it.
  // TODO: If there are multiple aliases to the same pointer, all aliases
  // should have their meta extended to this point!
  // TODO: Dataflow.
}

static void metadata_extend_operand_lifetime_on_use(PG_DYN(Metadata) metadata,
                                                    IrOperand op,
                                                    InstructionIndex ins_idx) {
  // No-op.
  if (IR_OPERAND_KIND_VREG != op.kind) {
    return;
  }
  metadata_extend_lifetime_on_use(metadata, op.u.vreg_meta_idx, ins_idx);
}

[[nodiscard]]
static PgString
register_constraint_to_str(VirtualRegisterConstraint constraint) {
  switch (constraint) {
  case VREG_CONSTRAINT_NONE:
    return PG_S("NONE");
  case VREG_CONSTRAINT_CONDITION_FLAGS:
    return PG_S("CONDITION_FLAGS");
  case VREG_CONSTRAINT_SYSCALL_NUM:
    return PG_S("SYSCALL_NUM");
  case VREG_CONSTRAINT_SYSCALL0:
    return PG_S("SYSCALL0");
  case VREG_CONSTRAINT_SYSCALL1:
    return PG_S("SYSCALL1");
  case VREG_CONSTRAINT_SYSCALL2:
    return PG_S("SYSCALL2");
  case VREG_CONSTRAINT_SYSCALL3:
    return PG_S("SYSCALL3");
  case VREG_CONSTRAINT_SYSCALL4:
    return PG_S("SYSCALL4");
  case VREG_CONSTRAINT_SYSCALL5:
    return PG_S("SYSCALL5");
  case VREG_CONSTRAINT_SYSCALL_RET:
    return PG_S("SYSCALL_RET");

  default:
    PG_ASSERT(0);
  }
}

static void ir_print_operand(IrOperand operand, PG_DYN(Metadata) metadata,
                             PgWriter *w, PgAllocator *allocator) {

  switch (operand.kind) {
  case IR_OPERAND_KIND_NUM:
    (void)pg_writer_write_u64_as_string(w, operand.u.u64, allocator);
    break;

  case IR_OPERAND_KIND_LABEL:
    PG_ASSERT(operand.u.label.value.len);
    (void)pg_writer_write_full(w, operand.u.label.value, allocator);
    break;

  case IR_OPERAND_KIND_VREG: {
    MetadataIndex meta_idx = operand.u.vreg_meta_idx;
    VirtualRegister vreg =
        PG_SLICE_AT(metadata, meta_idx.value).virtual_register;
    PG_ASSERT(vreg.value);

    (void)pg_writer_write_full(w, PG_S("v"), allocator);
    (void)pg_writer_write_u64_as_string(w, vreg.value, allocator);
  } break;

  case IR_OPERAND_KIND_NONE:
  default:
    PG_ASSERT(0);
  }
}

static void metadata_print_var(Metadata meta, PgWriter *w,
                               PgAllocator *allocator) {
  if (meta.identifier.len) {
    (void)pg_writer_write_full(w, meta.identifier, allocator);
  } else {
    (void)pg_writer_write_full(w, PG_S("v"), allocator);
    (void)pg_writer_write_u64_as_string(w, meta.virtual_register.value,
                                        allocator);
  }
}

static void metadata_print_meta(Metadata meta, PgWriter *w,
                                PgAllocator *allocator) {
  (void)pg_writer_write_full(w, PG_S("identifier=`"), allocator);
  (void)pg_writer_write_full(w, meta.identifier, allocator);
  (void)pg_writer_write_full(w, PG_S("` "), allocator);

  (void)pg_writer_write_full(w, PG_S("lifetime=["), allocator);
  (void)pg_writer_write_u64_as_string(w, meta.lifetime_start.value, allocator);
  (void)pg_writer_write_full(w, PG_S(":"), allocator);
  (void)pg_writer_write_u64_as_string(w, meta.lifetime_end.value, allocator);
  (void)pg_writer_write_full(w, PG_S("]"), allocator);

  if (meta.virtual_register.value) {
    (void)pg_writer_write_full(w, PG_S(" vreg=v"), allocator);
    (void)pg_writer_write_u64_as_string(w, meta.virtual_register.value,
                                        allocator);
    (void)pg_writer_write_full(w, PG_S(" constraint="), allocator);
    (void)pg_writer_write_full(
        w, register_constraint_to_str(meta.virtual_register.constraint),
        allocator);
    (void)pg_writer_write_full(w, PG_S(" addressed="), allocator);
    (void)pg_writer_write_full(
        w, meta.virtual_register.addressed ? PG_S("true") : PG_S("false"),
        allocator);
  }

  if (MEMORY_LOCATION_KIND_NONE != meta.memory_location.kind) {
    (void)pg_writer_write_full(w, PG_S(" mem_loc="), allocator);

    switch (meta.memory_location.kind) {
    case MEMORY_LOCATION_KIND_REGISTER:
    case MEMORY_LOCATION_KIND_STATUS_REGISTER:
      (void)pg_writer_write_full(w, PG_S("reg(todo)"), allocator);
      // TODO
#if 0
      amd64_print_register(meta.memory_location.reg);
#endif
      break;
    case MEMORY_LOCATION_KIND_STACK: {
      (void)pg_writer_write_full(w, PG_S("[sp"), allocator);
      i32 offset = meta.memory_location.u.base_pointer_offset;
      (void)pg_writer_write_full(w, PG_S("-"), allocator);
      (void)pg_writer_write_u64_as_string(w, (u64)offset, allocator);
    } break;
    case MEMORY_LOCATION_KIND_NONE:
    default:
      PG_ASSERT(0);
    }
  }
}

static void ir_print_instructions(PG_DYN(IrInstruction) instructions,
                                  PG_DYN(Metadata) metadata, PgWriter *w,
                                  PgAllocator *allocator) {
  for (u32 i = 0; i < instructions.len; i++) {
    (void)pg_writer_write_full(w, PG_S("["), allocator);
    (void)pg_writer_write_u64_as_string(w, i, allocator);
    (void)pg_writer_write_full(w, PG_S("]"), allocator);

    IrInstruction ins = PG_SLICE_AT(instructions, i);
    origin_write(w, ins.origin, allocator);

    (void)pg_writer_write_full(w, PG_S(" "), allocator);

    switch (ins.kind) {
    case IR_INSTRUCTION_KIND_ADD: {
      PG_ASSERT(IR_OPERAND_KIND_NUM == ins.lhs.kind ||
                IR_OPERAND_KIND_VREG == ins.lhs.kind);
      PG_ASSERT(IR_OPERAND_KIND_NUM == ins.rhs.kind ||
                IR_OPERAND_KIND_VREG == ins.rhs.kind);

      VirtualRegister vreg =
          PG_SLICE_AT(metadata, ins.meta_idx.value).virtual_register;
      PG_ASSERT(vreg.value);

      Type *type = PG_SLICE_AT(metadata, ins.meta_idx.value).type;
      type_print(type, w, allocator);
      (void)pg_writer_write_full(w, PG_S(".add"), allocator);

      (void)pg_writer_write_full(w, PG_S(" v"), allocator);
      (void)pg_writer_write_u64_as_string(w, vreg.value, allocator);
      (void)pg_writer_write_full(w, PG_S(", "), allocator);

      ir_print_operand(ins.lhs, metadata, w, allocator);
      (void)pg_writer_write_full(w, PG_S(", "), allocator);
      ir_print_operand(ins.rhs, metadata, w, allocator);
    } break;

    case IR_INSTRUCTION_KIND_COMPARISON: {
      PG_ASSERT(IR_OPERAND_KIND_NUM == ins.lhs.kind ||
                IR_OPERAND_KIND_VREG == ins.lhs.kind);
      PG_ASSERT(IR_OPERAND_KIND_NUM == ins.rhs.kind ||
                IR_OPERAND_KIND_VREG == ins.rhs.kind);

      VirtualRegister vreg =
          PG_SLICE_AT(metadata, ins.meta_idx.value).virtual_register;
      PG_ASSERT(vreg.value);

      Type *type = PG_SLICE_AT(metadata, ins.meta_idx.value).type;
      type_print(type, w, allocator);
      (void)pg_writer_write_full(w, PG_S(".cmp"), allocator);

      (void)pg_writer_write_full(w, PG_S(" v"), allocator);
      (void)pg_writer_write_u64_as_string(w, vreg.value, allocator);
      (void)pg_writer_write_full(w, PG_S(", "), allocator);

      ir_print_operand(ins.lhs, metadata, w, allocator);
      (void)pg_writer_write_full(w, PG_S(", "), allocator);
      ir_print_operand(ins.rhs, metadata, w, allocator);
    } break;

    case IR_INSTRUCTION_KIND_MOV: {
      PG_ASSERT(IR_OPERAND_KIND_VREG == ins.lhs.kind);
      PG_ASSERT(IR_OPERAND_KIND_NUM == ins.rhs.kind ||
                IR_OPERAND_KIND_VREG == ins.rhs.kind);

      VirtualRegister vreg =
          PG_SLICE_AT(metadata, ins.meta_idx.value).virtual_register;
      PG_ASSERT(vreg.value);

      Type *type = PG_SLICE_AT(metadata, ins.meta_idx.value).type;
      type_print(type, w, allocator);
      (void)pg_writer_write_full(w, PG_S(".mov"), allocator);

      (void)pg_writer_write_full(w, PG_S(" v"), allocator);
      (void)pg_writer_write_u64_as_string(w, vreg.value, allocator);
      (void)pg_writer_write_full(w, PG_S(", "), allocator);

      ir_print_operand(ins.rhs, metadata, w, allocator);
    } break;

    case IR_INSTRUCTION_KIND_LOAD_ADDRESS: {
      PG_ASSERT(IR_OPERAND_KIND_VREG == ins.lhs.kind);
      PG_ASSERT(IR_OPERAND_KIND_VREG == ins.rhs.kind);

      VirtualRegister vreg =
          PG_SLICE_AT(metadata, ins.meta_idx.value).virtual_register;
      PG_ASSERT(vreg.value);

      Type *type = PG_SLICE_AT(metadata, ins.meta_idx.value).type;
      type_print(type, w, allocator);
      (void)pg_writer_write_full(w, PG_S(".load"), allocator);

      (void)pg_writer_write_full(w, PG_S(" v"), allocator);
      (void)pg_writer_write_u64_as_string(w, vreg.value, allocator);
      (void)pg_writer_write_full(w, PG_S(", "), allocator);

      ir_print_operand(ins.lhs, metadata, w, allocator);
      (void)pg_writer_write_full(w, PG_S(", "), allocator);
      ir_print_operand(ins.rhs, metadata, w, allocator);
    } break;

    case IR_INSTRUCTION_KIND_JUMP_IF_FALSE: {
      PG_ASSERT(IR_OPERAND_KIND_NONE != ins.lhs.kind);
      PG_ASSERT(IR_OPERAND_KIND_LABEL == ins.rhs.kind);

      (void)pg_writer_write_full(w, PG_S("JumpIfFalse "), allocator);

      ir_print_operand(ins.lhs, metadata, w, allocator);
      (void)pg_writer_write_full(w, PG_S(", "), allocator);
      ir_print_operand(ins.rhs, metadata, w, allocator);
    } break;

    case IR_INSTRUCTION_KIND_JUMP: {
      PG_ASSERT(IR_OPERAND_KIND_LABEL == ins.lhs.kind);
      PG_ASSERT(IR_OPERAND_KIND_NONE == ins.rhs.kind);

      (void)pg_writer_write_full(w, PG_S("Jump "), allocator);
      ir_print_operand(ins.lhs, metadata, w, allocator);
    } break;

    case IR_INSTRUCTION_KIND_SYSCALL: {
      PG_ASSERT(IR_OPERAND_KIND_NONE == ins.lhs.kind);
      PG_ASSERT(IR_OPERAND_KIND_NONE == ins.rhs.kind);
      PG_ASSERT(ins.args_count > 0);
      PG_ASSERT(ins.args_count <= max_syscall_args_count);

      Type *type = PG_SLICE_AT(metadata, ins.meta_idx.value).type;
      type_print(type, w, allocator);

      (void)pg_writer_write_full(w, PG_S(".syscall["), allocator);
      (void)pg_writer_write_u64_as_string(w, i, allocator);
      (void)pg_writer_write_full(w, PG_S("]"), allocator);

    } break;

    case IR_INSTRUCTION_KIND_LABEL_DEFINITION: {
      PG_ASSERT(IR_OPERAND_KIND_LABEL == ins.lhs.kind);
      PG_ASSERT(IR_OPERAND_KIND_NONE == ins.rhs.kind);

      (void)pg_writer_write_full(w, PG_S("Label "), allocator);
      ir_print_operand(ins.lhs, metadata, w, allocator);
    } break;
    case IR_INSTRUCTION_KIND_TRAP: {
      PG_ASSERT(IR_OPERAND_KIND_NONE == ins.lhs.kind);
      PG_ASSERT(IR_OPERAND_KIND_NONE == ins.rhs.kind);

      (void)pg_writer_write_full(w, PG_S("Trap"), allocator);
    } break;

    case IR_INSTRUCTION_KIND_NONE:
    default:
      PG_ASSERT(0);
    }

    if (ins.meta_idx.value) {
      (void)pg_writer_write_full(w, PG_S(" // "), allocator);
      metadata_print_meta(PG_SLICE_AT(metadata, ins.meta_idx.value), w,
                          allocator);
    }
    (void)pg_writer_write_full(w, PG_S("\n"), allocator);
  }
  (void)pg_writer_flush(w, allocator);
}

static void ir_print_fn_def(FnDefinition fn_def, PgWriter *w,
                            PgAllocator *allocator) {
  PG_ASSERT(fn_def.name.len);

  (void)pg_writer_write_full(w, fn_def.name, allocator);

  ir_print_instructions(fn_def.instructions, fn_def.metadata, w, allocator);

  (void)pg_writer_write_full(w, PG_S("\n\n"), allocator);
}

static void ir_print_fn_defs(PG_DYN(FnDefinition) fn_defs, PgWriter *w,
                             PgAllocator *allocator) {
  for (u32 i = 0; i < fn_defs.len; i++) {
    FnDefinition fn_def = PG_SLICE_AT(fn_defs, i);
    ir_print_fn_def(fn_def, w, allocator);
  }
}

[[nodiscard]] static IrOperand ir_make_synth_label(u32 *label_current,
                                                   PgAllocator *allocator) {
  IrOperand res = {0};
  res.kind = IR_OPERAND_KIND_LABEL;
  res.u.label.value = pg_string_concat(
      PG_S("."), pg_u64_to_string(++(*label_current), allocator), allocator);
  return res;
}

static void ir_compute_fn_def_lifetimes(FnDefinition fn_def) {
  for (u32 i = 0; i < fn_def.instructions.len; i++) {
    IrInstruction ins = PG_SLICE_AT(fn_def.instructions, i);
    InstructionIndex ins_idx = {i};

    switch (ins.kind) {
    case IR_INSTRUCTION_KIND_ADD:
    case IR_INSTRUCTION_KIND_MOV:
    case IR_INSTRUCTION_KIND_LOAD_ADDRESS:
    case IR_INSTRUCTION_KIND_JUMP_IF_FALSE:
    case IR_INSTRUCTION_KIND_COMPARISON:
    case IR_INSTRUCTION_KIND_LABEL_DEFINITION:
    case IR_INSTRUCTION_KIND_SYSCALL: {
      if (ins.meta_idx.value) {
        metadata_start_lifetime(fn_def.metadata, ins.meta_idx, ins_idx);
      }
      metadata_extend_operand_lifetime_on_use(fn_def.metadata, ins.lhs,
                                              ins_idx);
      metadata_extend_operand_lifetime_on_use(fn_def.metadata, ins.rhs,
                                              ins_idx);
    } break;

      // Nothing to do.
    case IR_INSTRUCTION_KIND_JUMP:
    case IR_INSTRUCTION_KIND_TRAP:
      break;

    case IR_INSTRUCTION_KIND_NONE:
    default:
      PG_ASSERT(0);
    }
  }

  // Sanity check.
  for (u32 i = 0; i < fn_def.instructions.len; i++) {
    IrInstruction ins = PG_SLICE_AT(fn_def.instructions, i);
    InstructionIndex start =
        PG_SLICE_AT(fn_def.metadata, ins.meta_idx.value).lifetime_start;
    InstructionIndex end =
        PG_SLICE_AT(fn_def.metadata, ins.meta_idx.value).lifetime_end;

    PG_ASSERT(start.value < fn_def.instructions.len);
    PG_ASSERT(end.value < fn_def.instructions.len);
    PG_ASSERT(start.value <= end.value);
  }
}

static void ir_compute_fn_defs_lifetimes(PG_DYN(FnDefinition) fn_defs) {
  for (u64 i = 0; i < fn_defs.len; i++) {
    FnDefinition fn_def = PG_SLICE_AT(fn_defs, i);
    ir_compute_fn_def_lifetimes(fn_def);
  }
}

[[nodiscard]] static IrLocalVar *ir_local_vars_find(PG_DYN(IrLocalVar)
                                                        local_vars,
                                                    PgString name,
                                                    PG_DYN(AstNode) nodes) {
  for (i64 i = (i64)local_vars.len - 1; i >= 0; i--) {
    IrLocalVar var = PG_SLICE_AT(local_vars, i);
    PgString identifier = PG_SLICE_AT(nodes, var.node_idx.value).u.s;
    if (pg_string_eq(identifier, name)) {
      return PG_SLICE_AT_PTR(&local_vars, i);
    }
  }
  return nullptr;
}

[[nodiscard]] static PG_DYN(FnDefinition)
    ir_emit_from_ast(IrEmitter *emitter, PG_DYN(AstNode) nodes,
                     PgAllocator *allocator) {
  PG_ASSERT(AST_NODE_KIND_FN_DEFINITION == PG_SLICE_AT(nodes, 0).kind);

  type_insert_builtin(&emitter->types, allocator);

  PG_DYN(FnDefinition) fn_defs = {0};
  FnDefinition fn_def = {0};

  u32 scope_depth = 0;
  PG_DYN(IrLocalVar) local_vars = {0};
  PG_DYN_ENSURE_CAP(&local_vars, 256, allocator);

  PG_DYN(MetadataIndex) stack = {0};
  PG_DYN_ENSURE_CAP(&stack, 512, allocator);

  for (u32 i = 0; i < nodes.len; i++) {
    AstNode node = PG_SLICE_AT(nodes, i);

    switch (node.kind) {
    case AST_NODE_KIND_BOOL: {
      Type *type = type_upsert(&emitter->types, PG_S("bool"), nullptr);
      PG_ASSERT(type);

      IrInstruction ins = {0};
      ins.kind = IR_INSTRUCTION_KIND_MOV;
      ins.origin = node.origin;
      ins.meta_idx = metadata_make(&fn_def.metadata, type, allocator);
      ins.lhs = (IrOperand){
          .kind = IR_OPERAND_KIND_VREG,
          .u.vreg_meta_idx = ins.meta_idx,
      };
      ins.rhs = (IrOperand){
          .kind = IR_OPERAND_KIND_NUM,
          .u.u64 = node.u.n64,
      };
      PG_DYN_PUSH(&fn_def.instructions, ins, allocator);

      PG_DYN_PUSH(&stack, ins.meta_idx, allocator);

    } break;

    case AST_NODE_KIND_NUMBER: {
      // TODO: Refine exact numerical type.
      Type *type = type_upsert(&emitter->types, PG_S("u64"), nullptr);
      PG_ASSERT(type);

      IrInstruction ins = {0};
      ins.kind = IR_INSTRUCTION_KIND_MOV;
      ins.origin = node.origin;
      ins.meta_idx = metadata_make(&fn_def.metadata, type, allocator);
      ins.lhs = (IrOperand){
          .kind = IR_OPERAND_KIND_VREG,
          .u.vreg_meta_idx = ins.meta_idx,
      };
      ins.rhs = (IrOperand){
          .kind = IR_OPERAND_KIND_NUM,
          .u.u64 = node.u.n64,
      };
      PG_DYN_PUSH(&fn_def.instructions, ins, allocator);

      PG_DYN_PUSH(&stack, ins.meta_idx, allocator);
    } break;

    case AST_NODE_KIND_IDENTIFIER: {
      PgString name = node.u.s;
      PG_ASSERT(name.len);

      IrLocalVar *var = ir_local_vars_find(local_vars, name, nodes);
      if (!var) {
        Error err = {
            .kind = ERROR_KIND_VAR_UNDEFINED,
            .origin = node.origin,
            .src = emitter->src,
            .src_span =
                PG_SLICE_RANGE(emitter->src, node.origin.file_offset_start,
                               node.origin.file_offset_start + node.u.s.len),
        };
        PG_DYN_PUSH(emitter->errors, err, allocator);

        // Pseudo-define the undefined variable to improve error messages
        // downstream and preserve invariants.
        Type *type = type_upsert(&emitter->types, PG_S("void"), nullptr);
        PG_ASSERT(type);
        MetadataIndex meta_idx =
            metadata_make(&fn_def.metadata, type, allocator);
        PG_SLICE_LAST_PTR(&fn_def.metadata)->identifier = name;
        PG_DYN_PUSH(&stack, meta_idx, allocator);
        continue;
      }
      PG_ASSERT(var->type);

      IrInstruction ins = {0};
      ins.kind = IR_INSTRUCTION_KIND_MOV;
      ins.origin = node.origin;
      ins.meta_idx = metadata_make(&fn_def.metadata, var->type, allocator);
      PG_SLICE_LAST(fn_def.metadata).virtual_register.addressable = true;

      ins.lhs = (IrOperand){
          .kind = IR_OPERAND_KIND_VREG,
          .u.vreg_meta_idx = ins.meta_idx,
      };
      ins.rhs = (IrOperand){
          .kind = IR_OPERAND_KIND_VREG,
          .u.vreg_meta_idx = var->meta_idx,
      };

      PG_DYN_PUSH(&fn_def.instructions, ins, allocator);

      PG_DYN_PUSH(&stack, ins.meta_idx, allocator);
    } break;

    case AST_NODE_KIND_ADD: {
      MetadataIndex rhs_meta_idx = PG_DYN_POP(&stack);
      MetadataIndex lhs_meta_idx = PG_DYN_POP(&stack);

      Type *rhs_type = PG_SLICE_AT(fn_def.metadata, rhs_meta_idx.value).type;
      Type *lhs_type = PG_SLICE_AT(fn_def.metadata, lhs_meta_idx.value).type;
      PG_ASSERT(rhs_type);
      PG_ASSERT(lhs_type);

      if (!type_compatible(lhs_type, rhs_type)) {
        Pgu8Dyn sb = pg_string_builder_make(128, allocator);
        PG_DYN_APPEND_SLICE(&sb, PG_S("types are not compatible: "), allocator);
        PG_DYN_APPEND_SLICE(&sb, lhs_type->name, allocator);
        PG_DYN_APPEND_SLICE(&sb, PG_S(" and "), allocator);
        PG_DYN_APPEND_SLICE(&sb, rhs_type->name, allocator);

        Error err = {
            .kind = ERROR_KIND_TYPE_MISMATCH,
            .origin = node.origin,
            .src = emitter->src,
            .src_span = PG_SLICE_RANGE(
                emitter->src, node.origin.file_offset_start,
                // FIXME: origin should have a src_span directly.
                node.origin.file_offset_start + PG_S("assert(").len),
            .explanation = PG_DYN_TO_SLICE(PgString, sb),
        };
        PG_DYN_PUSH(emitter->errors, err, allocator);
      }

      IrInstruction ins = {0};
      ins.kind = IR_INSTRUCTION_KIND_ADD;
      ins.origin = node.origin;
      ins.meta_idx = metadata_make(&fn_def.metadata, lhs_type, allocator);

      ins.lhs = (IrOperand){
          .kind = IR_OPERAND_KIND_VREG,
          .u.vreg_meta_idx = lhs_meta_idx,
      };
      ins.rhs = (IrOperand){
          .kind = IR_OPERAND_KIND_VREG,
          .u.vreg_meta_idx = rhs_meta_idx,
      };

      PG_DYN_PUSH(&fn_def.instructions, ins, allocator);

      PG_DYN_PUSH(&stack, ins.meta_idx, allocator);
    } break;

    case AST_NODE_KIND_COMPARISON: {
      MetadataIndex rhs_meta_idx = PG_DYN_POP(&stack);
      MetadataIndex lhs_meta_idx = PG_DYN_POP(&stack);

      Type *rhs_type = PG_SLICE_AT(fn_def.metadata, rhs_meta_idx.value).type;
      Type *lhs_type = PG_SLICE_AT(fn_def.metadata, lhs_meta_idx.value).type;
      PG_ASSERT(rhs_type);
      PG_ASSERT(lhs_type);

      if (!type_compatible(lhs_type, rhs_type)) {
        Pgu8Dyn sb = pg_string_builder_make(128, allocator);
        PG_DYN_APPEND_SLICE(&sb, PG_S("types are not compatible: "), allocator);
        PG_DYN_APPEND_SLICE(&sb, lhs_type->name, allocator);
        PG_DYN_APPEND_SLICE(&sb, PG_S(" and "), allocator);
        PG_DYN_APPEND_SLICE(&sb, rhs_type->name, allocator);

        Error err = {
            .kind = ERROR_KIND_TYPE_MISMATCH,
            .origin = node.origin,
            .src = emitter->src,
            .src_span = PG_SLICE_RANGE(
                emitter->src, node.origin.file_offset_start,
                // FIXME: origin should have a src_span directly.
                node.origin.file_offset_start + PG_S("assert(").len),
            .explanation = PG_DYN_TO_SLICE(PgString, sb),
        };
        PG_DYN_PUSH(emitter->errors, err, allocator);
      }

      Type *type = type_upsert(&emitter->types, PG_S("bool"), nullptr);
      PG_ASSERT(type);

      IrInstruction ins = {0};
      ins.kind = IR_INSTRUCTION_KIND_COMPARISON;
      ins.origin = node.origin;
      ins.meta_idx = metadata_make(&fn_def.metadata, type, allocator);

      ins.lhs = (IrOperand){
          .kind = IR_OPERAND_KIND_VREG,
          .u.vreg_meta_idx = lhs_meta_idx,
      };
      ins.rhs = (IrOperand){
          .kind = IR_OPERAND_KIND_VREG,
          .u.vreg_meta_idx = rhs_meta_idx,
      };

      PG_DYN_PUSH(&fn_def.instructions, ins, allocator);

      PG_DYN_PUSH(&stack, ins.meta_idx, allocator);
    } break;

    case AST_NODE_KIND_BLOCK: {
      PG_ASSERT(0 && "todo");
    } break;

    case AST_NODE_KIND_VAR_DEFINITION: {
      PG_ASSERT(fn_def.instructions.len > 0);
      PgString name = node.u.s;
      PG_ASSERT(name.len);

      IrLocalVar *var = ir_local_vars_find(local_vars, name, nodes);
      if (var) {
        Error err = {
            .kind = ERROR_KIND_VAR_SHADOWING,
            .origin = node.origin,
            .src = emitter->src,
            .src_span =
                PG_SLICE_RANGE(emitter->src, node.origin.file_offset_start,
                               node.origin.file_offset_start + node.u.s.len),
        };
        // TODO: Include `var` in the error!
        PG_DYN_PUSH(emitter->errors, err, allocator);
      }

      MetadataIndex op_meta_idx = PG_DYN_POP(&stack);
      Type *op_type = PG_SLICE_AT(fn_def.metadata, op_meta_idx.value).type;
      PG_ASSERT(op_type);

      // TODO: Check if a type was explicitly given.
      Type *type = op_type;

      IrInstruction ins = {0};
      ins.kind = IR_INSTRUCTION_KIND_MOV;
      ins.origin = node.origin;
      ins.meta_idx = metadata_make(&fn_def.metadata, type, allocator);
      PG_SLICE_LAST_PTR(&fn_def.metadata)->identifier = name;

      PG_DYN_PUSH(&local_vars,
                  ((IrLocalVar){
                      .node_idx = {i},
                      .scope_depth = scope_depth,
                      .meta_idx = ins.meta_idx,
                      .type = type,
                  }),
                  allocator);

      ins.lhs = (IrOperand){
          .kind = IR_OPERAND_KIND_VREG,
          .u.vreg_meta_idx = ins.meta_idx,
      };
      ins.rhs = (IrOperand){
          .kind = IR_OPERAND_KIND_VREG,
          .u.vreg_meta_idx = op_meta_idx,
      };

      PG_DYN_PUSH(&fn_def.instructions, ins, allocator);
    } break;

    case AST_NODE_KIND_ADDRESS_OF: {
      PG_ASSERT(fn_def.instructions.len >= 1);

      MetadataIndex op_meta_idx = PG_DYN_POP(&stack);
      Metadata op_meta = PG_SLICE_AT(fn_def.metadata, op_meta_idx.value);
      Type *op_type = op_meta.type;
      PG_ASSERT(op_type);

      if (!op_meta.virtual_register.addressable) {
        Error err = {
            .kind = ERROR_KIND_ADDRESS_OF_RHS_NOT_ADDRESSABLE,
            .origin = node.origin,
            .src = emitter->src,
            .src_span =
                PG_SLICE_RANGE(emitter->src, node.origin.file_offset_start,
                               // FIXME: origin should have a src_span directly.
                               node.origin.file_offset_start + 1),
        };
        PG_DYN_PUSH(emitter->errors, err, allocator);
      }

      // TODO: When type `T` is explicitly given: check if `*T` == `op_type`.

      PgString type_name =
          pg_string_concat(PG_S("*"), op_type->name, allocator);
      Type *type = type_upsert(&emitter->types, type_name, allocator);
      PG_ASSERT(type);
      PG_ASSERT(type->ptr_level < UINT8_MAX);
      type->kind = op_type->kind;
      type->origin = fn_def.origin;
      type->ptr_level = op_type->ptr_level + 1;
      type->size = sizeof(u64);

      IrInstruction ins = {0};
      ins.kind = IR_INSTRUCTION_KIND_LOAD_ADDRESS;
      ins.origin = node.origin;
      ins.meta_idx = metadata_make(&fn_def.metadata, type, allocator);
      PG_SLICE_LAST(fn_def.metadata).virtual_register.addressable = true;

      PG_SLICE_AT_PTR(&fn_def.metadata, op_meta_idx.value)
          ->virtual_register.addressed = true;

      ins.lhs = (IrOperand){
          .kind = IR_OPERAND_KIND_VREG,
          .u.vreg_meta_idx = ins.meta_idx,
      };
      ins.rhs = (IrOperand){
          .kind = IR_OPERAND_KIND_VREG,
          .u.vreg_meta_idx = op_meta_idx,
      };
      PG_DYN_PUSH(&fn_def.instructions, ins, allocator);

      PG_DYN_PUSH(&stack, ins.meta_idx, allocator);
    } break;

    case AST_NODE_KIND_BRANCH: {
      PG_ASSERT(fn_def.instructions.len >= 1);

      IrInstruction ins_jmp_else = {0};
      ins_jmp_else.kind = IR_INSTRUCTION_KIND_JUMP_IF_FALSE;
      ins_jmp_else.origin = node.origin;

      MetadataIndex cond_meta_idx = PG_DYN_POP(&stack);
      Type *cond_type = PG_SLICE_AT(fn_def.metadata, cond_meta_idx.value).type;
      PG_ASSERT(cond_type);

      if (TYPE_KIND_BOOLEAN != cond_type->kind) {
        PG_ASSERT(0 && "todo");
      }

      AstNode end_label = PG_SLICE_AT(nodes, i - 1);
      AstNode else_label = PG_SLICE_AT(nodes, i - 2);
      AstNode then_label = PG_SLICE_AT(nodes, i - 3);
      PG_ASSERT(AST_NODE_KIND_LABEL == end_label.kind);
      PG_ASSERT(AST_NODE_KIND_LABEL == else_label.kind);
      PG_ASSERT(AST_NODE_KIND_LABEL == then_label.kind);
      PG_ASSERT(then_label.u.label.value.len);
      PG_ASSERT(else_label.u.label.value.len);

      ins_jmp_else.lhs = (IrOperand){
          .kind = IR_OPERAND_KIND_VREG,
          .u.vreg_meta_idx = cond_meta_idx,
      };
      ins_jmp_else.rhs = (IrOperand){
          .kind = IR_OPERAND_KIND_LABEL,
          .u.label = else_label.u.label,
      };
      PG_DYN_PUSH(&fn_def.instructions, ins_jmp_else, allocator);
    } break;

    case AST_NODE_KIND_JUMP: {
      PG_ASSERT(fn_def.instructions.len > 0);

      AstNode op = PG_SLICE_AT(nodes, i - 1);
      PG_ASSERT(AST_NODE_KIND_LABEL == op.kind);

      IrInstruction ins = {0};
      ins.kind = IR_INSTRUCTION_KIND_JUMP;
      ins.origin = node.origin;
      ins.lhs = (IrOperand){
          .kind = IR_OPERAND_KIND_LABEL,
          .u.label = op.u.label,
      };
      PG_DYN_PUSH(&fn_def.instructions, ins, allocator);

    } break;

    case AST_NODE_KIND_LABEL:
      break;

    case AST_NODE_KIND_BUILTIN_TRAP: {
      IrInstruction ins = {0};
      ins.kind = IR_INSTRUCTION_KIND_TRAP;
      ins.origin = node.origin;
      PG_DYN_PUSH(&fn_def.instructions, ins, allocator);
    } break;

    case AST_NODE_KIND_FN_DEFINITION: {
      if (fn_def.instructions.len > 0) {
        PG_DYN_PUSH(&fn_defs, fn_def, allocator);
      }

      local_vars.len = 0;
      stack.len = 0;

      PgString name = node.u.s;
      PG_ASSERT(name.len);

      fn_def = (FnDefinition){
          .origin = node.origin,
          .name = name,
      };
      PG_DYN_ENSURE_CAP(&fn_def.instructions, nodes.len * 2, allocator);
      PG_DYN_ENSURE_CAP(&fn_def.metadata, nodes.len, allocator);
      // Dummy.
      PG_DYN_PUSH(&fn_def.metadata, (Metadata){0}, allocator);

      if (node.flags & AST_NODE_FLAG_GLOBAL) {
        fn_def.flags = IR_FLAG_GLOBAL;
      }

      Type *type = type_upsert(&emitter->types, fn_def.name, allocator);
      PG_ASSERT(type);
      type->kind = TYPE_KIND_FN_DEF;
      type->origin = fn_def.origin;

    } break;

    case AST_NODE_KIND_SYSCALL: {
      PG_ASSERT(node.u.stack_args_count > 0);
      PG_ASSERT(node.u.stack_args_count <= max_syscall_args_count);

      // TODO: Set constraint on args vregs.
      for (i64 j = node.u.stack_args_count - 1; j >= 0; j--) {
        MetadataIndex arg_meta_idx = PG_DYN_POP(&stack);
        PG_SLICE_AT_PTR(&fn_def.metadata, arg_meta_idx.value)
            ->virtual_register.constraint =
            (VirtualRegisterConstraint)((i64)VREG_CONSTRAINT_SYSCALL_NUM + j);
      }

      Type *type = type_upsert(&emitter->types, PG_S("u64"), nullptr);
      PG_ASSERT(type);

      IrInstruction ins = {0};
      ins.kind = IR_INSTRUCTION_KIND_SYSCALL;
      ins.origin = node.origin;
      ins.args_count = (u8)node.u.stack_args_count;
      ins.meta_idx = metadata_make(&fn_def.metadata, type, allocator);
      PG_SLICE_LAST_PTR(&fn_def.metadata)->virtual_register.constraint =
          VREG_CONSTRAINT_SYSCALL_RET;
      // TODO: args_count.

      PG_DYN_PUSH(&fn_def.instructions, ins, allocator);

      PG_DYN_PUSH(&stack, ins.meta_idx, allocator);
    } break;

    case AST_NODE_KIND_LABEL_DEFINITION: {
      // TODO: Support labels with names predefined in the source.
      PG_ASSERT(node.u.label.value.len);

      IrInstruction ins = {0};
      ins.kind = IR_INSTRUCTION_KIND_LABEL_DEFINITION;
      ins.origin = node.origin;
      ins.lhs = (IrOperand){
          .kind = IR_OPERAND_KIND_LABEL,
          .u.label = node.u.label,
      };
#if 0
      ins.meta_idx = metadata_make(&fn_def.metadata, allocator);
      PG_SLICE_LAST_PTR(&fn_def.metadata)->label = ins.lhs.u.label;
#endif

      PG_DYN_PUSH(&fn_def.instructions, ins, allocator);
    } break;

    case AST_NODE_KIND_BUILTIN_PRINTLN: {
      PG_ASSERT(fn_def.instructions.len >= 1);

      MetadataIndex cond_meta_idx = PG_DYN_POP(&stack);
      // FIXME: Add negation of condition!

      Type *cond_type = PG_SLICE_AT(fn_def.metadata, cond_meta_idx.value).type;
      PG_ASSERT(cond_type);

      if (TYPE_KIND_BOOLEAN != cond_type->kind) {
        Pgu8Dyn sb = pg_string_builder_make(128, allocator);
        PG_DYN_APPEND_SLICE(&sb, PG_S("expected bool, got "), allocator);
        PG_DYN_APPEND_SLICE(&sb, cond_type->name, allocator);

        Error err = {
            .kind = ERROR_KIND_TYPE_MISMATCH,
            .origin = node.origin,
            .src = emitter->src,
            .src_span = PG_SLICE_RANGE(
                emitter->src, node.origin.file_offset_start,
                // FIXME: origin should have a src_span directly.
                node.origin.file_offset_start + PG_S("assert(").len),
            .explanation = PG_DYN_TO_SLICE(PgString, sb),
        };
        PG_DYN_PUSH(emitter->errors, err, allocator);
      }
      PG_ASSERT(0 && "todo");
    } break;
    case AST_NODE_KIND_BUILTIN_ASSERT: {
      PG_ASSERT(fn_def.instructions.len >= 1);

      MetadataIndex cond_meta_idx = PG_DYN_POP(&stack);
      // FIXME: Add negation of condition!

      Type *cond_type = PG_SLICE_AT(fn_def.metadata, cond_meta_idx.value).type;
      PG_ASSERT(cond_type);

      if (TYPE_KIND_BOOLEAN != cond_type->kind) {
        Pgu8Dyn sb = pg_string_builder_make(128, allocator);
        PG_DYN_APPEND_SLICE(&sb, PG_S("expected bool, got "), allocator);
        PG_DYN_APPEND_SLICE(&sb, cond_type->name, allocator);

        Error err = {
            .kind = ERROR_KIND_TYPE_MISMATCH,
            .origin = node.origin,
            .src = emitter->src,
            .src_span = PG_SLICE_RANGE(
                emitter->src, node.origin.file_offset_start,
                // FIXME: origin should have a src_span directly.
                node.origin.file_offset_start + PG_S("assert(").len),
            .explanation = PG_DYN_TO_SLICE(PgString, sb),
        };
        PG_DYN_PUSH(emitter->errors, err, allocator);
      }

      IrOperand if_end_target =
          ir_make_synth_label(&emitter->label_id, allocator);

      IrInstruction ins_jmp = {0};
      ins_jmp.kind = IR_INSTRUCTION_KIND_JUMP_IF_FALSE;
      ins_jmp.origin = node.origin;
      ins_jmp.lhs = (IrOperand){
          .kind = IR_OPERAND_KIND_VREG,
          .u.vreg_meta_idx = cond_meta_idx,
      };
      // TODO: rflags constraint?
      ins_jmp.rhs = if_end_target;
      PG_DYN_PUSH(&fn_def.instructions, ins_jmp, allocator);

      IrInstruction ins_trap = {0};
      ins_trap.kind = IR_INSTRUCTION_KIND_TRAP;
      ins_trap.origin = node.origin;
      PG_DYN_PUSH(&fn_def.instructions, ins_trap, allocator);

      IrInstruction ins_if_end_label = {0};
      ins_if_end_label.kind = IR_INSTRUCTION_KIND_LABEL_DEFINITION;
      ins_if_end_label.origin = node.origin;
      ins_if_end_label.lhs = if_end_target;
      PG_DYN_PUSH(&fn_def.instructions, ins_if_end_label, allocator);
    } break;

    case AST_NODE_KIND_NONE:
    default:
      PG_ASSERT(0);
    }
  }

  if (fn_def.instructions.len > 0) {
    PG_DYN_PUSH(&fn_defs, fn_def, allocator);
  }

  ir_compute_fn_defs_lifetimes(fn_defs);

  return fn_defs;
}
