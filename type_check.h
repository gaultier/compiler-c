#pragma once

#include "origin.h"

typedef enum {
  TYPE_KIND_NONE,
  TYPE_KIND_BOOLEAN,
  TYPE_KIND_NUMBER,
  TYPE_KIND_FN_DEF,
  // More...
} TypeKind;

typedef struct Type Type;
struct Type {
  TypeKind kind;
  u64 size;
  Origin origin;
  u8 ptr_level;

  // Hash trie fields.
  PgString name; // Key.
  Type *child[4];
};

typedef struct {
  u32 value;
} TypeIdx;

#if 0
static const Type types_builtin[] = {
    {0}, // Dummy
    {.name = PG_S("u64"), .size = sizeof(u64)},
    {.name = PG_S("bool"), .size = 1},
};

typedef struct {
  TypeDyn types;
} TypeChecker;

[[nodiscard]] static TypeChecker
types_make_type_checker(PgAllocator *allocator) {
  TypeChecker type_checker = {0};

  *PG_DYN_PUSH(&type_checker.types, allocator) = (Type){0}; // Dummy
  *PG_DYN_PUSH(&type_checker.types, allocator) =
      (Type){.name = PG_S("u64"), .size = sizeof(u64)};
  *PG_DYN_PUSH(&type_checker.types, allocator) =
      (Type){.name = PG_S("bool"), .size = 1};

  return type_checker;
}
#endif

[[nodiscard]] static Type *type_upsert(Type **htrie, PgString name,
                                       PgAllocator *allocator) {
  for (u64 h = pg_hash_fnv(name); *htrie; h <<= 2) {
    if (pg_string_eq(name, (*htrie)->name)) {
      return *htrie;
    }
    htrie = &(*htrie)->child[h >> 62];
  }
  if (!allocator) {
    return nullptr;
  }

  *htrie = pg_alloc(allocator, sizeof(Type), _Alignof(Type), 1);
  (*htrie)->name = name;

  return (*htrie);
}

static void type_print(Type *type) {
  if (!type) {
    printf("any");
    return;
  }

  for (u8 i = 0; i < type->ptr_level; i++) {
    printf("*");
  }

  printf("%.*s", (i32)type->name.len, type->name.data);
}

[[nodiscard]] static bool type_compatible(Type *a, Type *b) {
  // TODO: Allow implicit downcasting, etc?
  return a == b;
}

static void type_insert_builtin(Type **types, PgAllocator *allocator) {
  Type *type_bool = type_upsert(types, PG_S("bool"), allocator);
  PG_ASSERT(type_bool);
  type_bool->kind = TYPE_KIND_BOOLEAN;
  type_bool->size = 1;

  Type *type_u64 = type_upsert(types, PG_S("u64"), allocator);
  PG_ASSERT(type_u64);
  type_u64->kind = TYPE_KIND_NUMBER;
  type_u64->size = sizeof(u64);
}
