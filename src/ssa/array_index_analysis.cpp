/*******************************************************************\

Module: Analysis of expressions used as array indices

Author: Viktor Malik, imalik@fit.vutbr.cz

\*******************************************************************/

/// \file
/// Analysis of expressions used as array indices

#include "array_index_analysis.h"

#include <langapi/language_util.h>

#include "ssa_dereference.h"
#include "ssa_object.h"

void array_index_domaint::transform(const irep_idt &function_from,
                                    trace_ptrt trace_from,
                                    const irep_idt &function_to,
                                    trace_ptrt trace_to,
                                    ai_baset &ai,
                                    const namespacet &ns)
{
  locationt from(trace_from->current_location());

  if(from->is_assign())
  {
    collect_lhs_indices(from->assign_lhs(), from, ai, ns);
    collect_rhs_indices(from->assign_rhs(), from, ai, ns);
  }
  else if(from->is_goto() || from->is_assert())
  {
    collect_rhs_indices(from->condition(), from, ai, ns);
  }
}

bool array_index_domaint::merge(const array_index_domaint &other,
                                trace_ptrt trace_from,
                                trace_ptrt trace_to)
{
  bool result = has_values.is_false() && !other.has_values.is_false();
  has_values = tvt::unknown();
  for(auto &other_array_indices : other.written_indices)
  {
    auto array_indices = written_indices.find(other_array_indices.first);
    if(array_indices == written_indices.end())
    {
      // Array has not been assigned to before - copy all indices
      written_indices.emplace(other_array_indices.first,
                              other_array_indices.second);
      result = true;
    }
    else
    {
      // Array has been assigned to before - do union of indices
      size_t old_size = array_indices->second.size();
      array_indices->second.insert(other_array_indices.second.begin(),
                                   other_array_indices.second.end());
      if(array_indices->second.size() != old_size)
        result = true;
    }
  }
  return result;
}

void array_index_domaint::collect_lhs_indices(const exprt &expr,
                                              locationt loc,
                                              ai_baset &ai,
                                              const namespacet &ns)
{
  collect_indices(expr, loc, ai, ns, written_indices);
}

void array_index_domaint::collect_rhs_indices(const exprt &expr,
                                              locationt loc,
                                              ai_baset &ai,
                                              const namespacet &ns)
{
  auto &read_indices = dynamic_cast<array_index_analysist &>(ai).read_indices;
  collect_indices(expr, loc, ai, ns, read_indices);
}

void array_index_domaint::add_index(const exprt &array,
                                    const exprt &index,
                                    locationt loc,
                                    const namespacet &ns,
                                    index_mapt &dest_map)
{
  ssa_objectt array_obj(array, ns);
  if(array_obj)
  {
    dest_map[array_obj.get_identifier()].emplace(index, loc);
  }
  else if(array.id() == ID_typecast)
    add_index(to_typecast_expr(array).op(), index, loc, ns, dest_map);
  else if(array.id() == ID_if)
  {
    auto &if_expr = to_if_expr(array);
    add_index(if_expr.true_case(), index, loc, ns, dest_map);
    add_index(if_expr.false_case(), index, loc, ns, dest_map);
  }
}

void array_index_domaint::collect_indices(const exprt &expr,
                                          locationt loc,
                                          ai_baset &ai,
                                          const namespacet &ns,
                                          index_mapt &dest_map)
{
  if(expr.id() == ID_index)
  {
    auto &values =
      dynamic_cast<array_index_analysist &>(ai).value_analysis[loc];

    // Get array
    auto &array = to_index_expr(expr).array();
    exprt array_deref = dereference(array, values, "", ns, false);

    // Index may be a typecast
    exprt index = to_index_expr(expr).index();
    if(index.id() == ID_typecast)
      index = to_typecast_expr(index).op();

    add_index(array_deref, index, loc, ns, dest_map);
  }
  else
  {
    forall_operands(op, expr)
    {
      collect_indices(*op, loc, ai, ns, dest_map);
    }
  }
}

void array_index_domaint::output(std::ostream &out,
                                 const ai_baset &ai,
                                 const namespacet &ns) const
{
  for(auto &indices : written_indices)
  {
    out << indices.first << " (written) : ";
    for(auto &index_info : indices.second)
      out << " " << from_expr(ns, "", index_info.index);
    out << "\n";
  }
}

void array_index_analysist::output(const namespacet &ns,
                                   const irep_idt &function_identifier,
                                   const goto_programt &goto_program,
                                   std::ostream &out) const
{
  ai_baset::output(ns, function_identifier, goto_program, out);

  for(auto &indices : read_indices)
  {
    out << indices.first << " (read) : ";
    for(auto &index_info : indices.second)
      out << " " << from_expr(ns, "", index_info.index);
    out << "\n";
  }
}

void array_index_analysist::initialize(
  const irep_idt &function_id,
  const goto_functionst::goto_functiont &goto_function)
{
  ait<array_index_domaint>::initialize(function_id, goto_function);
  forall_goto_program_instructions(i_it, goto_function.body)
    get_state(i_it).make_bottom();
}
