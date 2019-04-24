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
#define ID_iterator "#iterator"
#define ID_it_pointer "#it_pointer"
#define ID_it_field "#it_field"
#define ID_it_field_cnt "#it_field_cnt"
#define ID_it_init_value "#it_init_value"
#define ID_it_init_value_level "#it_init_value_level"

symbol_exprt pointed_object(const exprt &expr, const namespacet &ns);

bool is_pointed(const exprt &expr);
bool is_iterator(const exprt &expr);

unsigned pointed_level(const exprt &expr);
unsigned it_value_level(const exprt &expr);

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
void copy_iterator(exprt &dest, const exprt &src);

const exprt symbolic_dereference(const exprt &expr, const namespacet &ns);
bool has_symbolic_deref(const exprt &expr);

void set_iterator_fields(exprt &dest, const std::vector<irep_idt> fields);
const std::vector<irep_idt> get_iterator_fields(const exprt &expr);

const irep_idt iterator_to_initial_id(
  const exprt &expr,
  const irep_idt &expr_id);

#endif // CPROVER_2LS_SSA_SSA_POINTED_OBJECTS_H
