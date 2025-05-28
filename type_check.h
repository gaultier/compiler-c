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

  PG_ASSERT(type->kind);
  PG_ASSERT(type->name.data);
  PG_ASSERT(type->name.len);

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
