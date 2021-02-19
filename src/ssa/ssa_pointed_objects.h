/*******************************************************************\

Module: Library of functions for working with pointed objects

Author: Viktor Malik

\*******************************************************************/
/// \file
/// Library of functions for working with pointed objects

#ifndef CPROVER_2LS_SSA_SSA_POINTED_OBJECTS_H
#define CPROVER_2LS_SSA_SSA_POINTED_OBJECTS_H

#include <util/expr.h>
#include <util/namespace.h>
#include <util/std_expr.h>

#define ID_pointed "#pointed"
#define ID_pointed_level "#level"
#define ID_pointer_id "id"
#define ID_pointer_subtype "subtype"
#define ID_pointer_sym "sym"
#define ID_pointer_compound "compound"
#define ID_pointer_field "field"

symbol_exprt pointed_object(const exprt &expr, const namespacet &ns);
bool is_pointed(const exprt &expr);
unsigned pointed_level(const exprt &expr);

const irep_idt pointer_root_id(const exprt &expr);
const irep_idt pointer_level_field(const exprt &expr, const unsigned level);
const std::vector<irep_idt> pointer_fields(
  const exprt &expr,
  const unsigned from_level);

const exprt get_pointer(const exprt &expr, unsigned level);
const exprt get_pointer_root(const exprt &expr, unsigned level);
const irep_idt get_pointer_id(const exprt &expr);

void copy_pointed_info(exprt &dest, const exprt &src, const unsigned max_level);
void copy_pointed_info(exprt &dest, const exprt &src);

const exprt symbolic_dereference(const exprt &expr, const namespacet &ns);
bool has_symbolic_deref(const exprt &expr);

#endif // CPROVER_2LS_SSA_SSA_POINTED_OBJECTS_H
