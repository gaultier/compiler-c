#pragma once
#include "type_check.h"

typedef struct {
  Type *type;
  Pgu8Slice text;
} ExternalFn;
PG_DYN(ExternalFn) ExternalFnDyn;
PG_RESULT(ExternalFnDyn) ExternalFnDynResult;

[[nodiscard]] static ExternalFnDynResult
pg_runtime_load_elf(Type **types, PgLogger *logger, PgAllocator *allocator) {
  ExternalFnDynResult res = {0};
  PG_DYN_ENSURE_CAP(&res.res, 128, allocator);

  PgString file_path = PG_S("runtime_amd64_linux.o");
  PgStringResult res_read = pg_file_read_full_from_path(file_path, allocator);
  if (res_read.err) {
    pg_log(logger, PG_LOG_LEVEL_ERROR, "failed to read runtime file",
           pg_log_c_err("err", res_read.err), pg_log_c_s("path", file_path));
    res.err = res_read.err;
    return res;
  }

  PgString runtime_bin = res_read.res;
  PgElfResult res_elf = pg_elf_parse(runtime_bin, allocator);
  if (res_elf.err) {
    pg_log(logger, PG_LOG_LEVEL_ERROR, "failed to parse runtime file",
           pg_log_c_err("err", res_elf.err), pg_log_c_s("path", file_path));
    res.err = res_elf.err;
    return res;
  }

  PgElf elf = res_elf.res;

  for (u64 i = 0; i < elf.symtab.len; i++) {
    PgElfSymbolTableEntry sym = PG_SLICE_AT(elf.symtab, i);

    if (PG_ELF_SYMBOL_TYPE_FUNC != pg_elf_symbol_get_type(sym)) {
      continue;
    }

    if (PG_ELF_SYMBOL_BIND_GLOBAL != pg_elf_symbol_get_bind(sym)) {
      continue;
    }

    Pgu8SliceResult res_text = pg_elf_symbol_get_program_text(elf, sym);
    if (res_text.err) {
      pg_log(logger, PG_LOG_LEVEL_ERROR,
             "failed to read program text for symbol",
             pg_log_c_err("err", res_text.err), pg_log_c_s("path", file_path));
      res.err = res_text.err;
      return res;
    }

    Pgu8Slice text = res_text.res;

    PgStringResult res_name = pg_elf_get_string_at(elf, sym.name);
    if (res_name.err) {
      res.err = res_name.err;
      return res;
    }
    PgString name = res_name.res;

    // HACK: Should be function signatures somewhere in `runtime.unicorn`.
    if (pg_string_eq(name, PG_S("builtin.println_u64"))) {
      ExternalFn ext_sym = {0};
      ext_sym.text = text;
      ext_sym.type = type_upsert(types, PG_S("void(u64)"), allocator);
      ext_sym.type->kind = TYPE_KIND_FN_DEF;
      ext_sym.type->size = sizeof(void *);

      *PG_DYN_PUSH(&res.res, allocator) = ext_sym;

      pg_log(logger, PG_LOG_LEVEL_DEBUG, "runtime: loaded external function",
             pg_log_c_s("name", name), pg_log_c_u64("text.len", text.len),
             pg_log_c_s("type", ext_sym.type->name));
    }
  }

  return res;
}
