/*******************************************************************\

Module: SSA for malloc()

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// SSA for malloc()

#ifndef CPROVER_2LS_SSA_MALLOC_SSA_H
#define CPROVER_2LS_SSA_MALLOC_SSA_H

#include <util/std_code.h>
#include <goto-programs/goto_model.h>

exprt malloc_ssa(
  const side_effect_exprt &,
  const std::string &suffix,
  symbol_tablet &,
  goto_programt &,
  goto_programt::targett &,
  bool is_concrete,
  bool alloc_concrete);

bool replace_malloc(
  goto_modelt &goto_model,
  const std::string &suffix,
  bool alloc_concrete);

exprt create_dynamic_object(
  const std::string &suffix,
  const typet &type,
  symbol_tablet &symbol_table,
  bool is_concrete);

std::vector<exprt> collect_pointer_vars(
  const symbol_tablet &symbol_table,
  const typet &pointed_type);

void allow_record_malloc(goto_modelt &goto_model);
void allow_record_memleak(goto_modelt &goto_model);
void split_memory_leak_assignments(
  goto_programt &goto_program,
  symbol_tablet &symbol_table);

#endif
