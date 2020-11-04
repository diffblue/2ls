/*******************************************************************\

Module: Abstract domain for representing contents of arrays

Author: Viktor Malik <viktor.malik@gmail.com>

\*******************************************************************/
/// \file
/// Abstract domain for representing contents of arrays

#include "array_domain.h"

#include <util/arith_tools.h>
#include <util/simplify_expr.h>

#include <ssa/local_ssa.h>

#include "strategy_solver_array.h"
#include "tpolyhedra_domain.h"

#include <algorithm>

unsigned array_domaint::segment_cnt = 0;

array_domaint::array_domaint(unsigned int domain_number,
                             replace_mapt &renaming_map,
                             const var_specst &var_specs,
                             const local_SSAt &SSA,
                             incremental_solvert *solver,
                             template_generator_baset &template_generator)
  : domaint(domain_number, renaming_map, SSA.ns), SSA(SSA), solver(solver)
{
  // Split arrays to segments and create a new set of var specs, each
  // representing one segment.
  make_segments(var_specs, SSA.ns);
  auto segment_var_specs = var_specs_from_segments();
  inner_domain =
    template_generator.instantiate_standard_domains(segment_var_specs, SSA);
}

/// Value initialization - initialize inner domains
void array_domaint::initialize_value(domaint::valuet &value)
{
  auto &array_value = dynamic_cast<array_valuet &>(value);
  inner_domain->initialize_value(*array_value.inner_value);
}

/// Create segmentation of all arrays used in var_specs.
void array_domaint::make_segments(const var_specst &var_specs,
                                  const namespacet &ns)
{
  var_specst result_var_specs;
  for(const var_spect &spec : var_specs)
  {
    if(spec.guards.kind != guardst::LOOP)
      continue;

    if(spec.var.type().id() == ID_array)
    {
      auto array_size = get_array_size(spec);
      auto &index_type = array_size.type();

      auto written_indices = spec.related_vars;
      if(order_indices(written_indices, array_size))
      { // Indices can be ordered - create a single segmentation
        // The first index border is {0}
        exprt last_border = make_zero(index_type);
        for(exprt index_var : written_indices)
        {
          index_var = simplify_expr(index_var, ns);
          // Ensure that all segment borders have the same type.
          if(index_var.type() != index_type)
            index_var = typecast_exprt(index_var, index_type);

          // For each index i, add two segments:
          // {last} ... {i}
          if(last_border != index_var)
            add_segment(spec, last_border, index_var);
          // {i} ... {i + 1}
          auto index_plus_one = simplify_expr(expr_plus_one(index_var), ns);
          add_segment(spec, index_var, index_plus_one);

          last_border = index_plus_one;
        }

        // The last segment is {last} ... {size}
        add_segment(spec, last_border, array_size);
      }
      else
      { // Indices cannot be ordered - create one segmentation for each index
        for(exprt index_var : written_indices)
        {
          // Ensure that all segment borders have the same type.
          if(index_var.type() != index_type)
            index_var = typecast_exprt(index_var, index_type);

          exprt index_plus_one = expr_plus_one(index_var);
          // For each written index i, create a segmentation:
          //   {0} ... {i] ... {i + 1} ... {size}
          add_segment(spec, make_zero(index_type), index_var);
          add_segment(spec, index_var, index_plus_one);
          add_segment(spec, index_plus_one, array_size);
        }
      }
      add_segment(spec, make_zero(index_type), array_size);
    }
  }
}

/// Add a single segment to the template.
/// New unique variables representing the segment index and element are created.
void array_domaint::add_segment(const var_spect &var_spec,
                                const exprt &lower,
                                const exprt &upper)
{
  const symbol_exprt &index_var =
    symbol_exprt("idx#" + std::to_string(segment_cnt), lower.type());
  const symbol_exprt &elem_var =
    symbol_exprt("elem#" + std::to_string(segment_cnt++),
                 to_array_type(var_spec.var.type()).subtype());
  segmentation_map[var_spec.var].emplace_back(
    var_spec, elem_var, index_var, lower, upper, get_array_size(var_spec));
}

/// Projection of the computed invariant on variables.
/// Includes mapping of segments onto read indices of corresponding arrays.
/// This ensures that the computed array invariant is applied every time when
/// reading from the given array.
void array_domaint::project_on_vars(domaint::valuet &base_value,
                                    const var_sett &vars,
                                    exprt &result)
{
  auto &array_value = dynamic_cast<array_valuet &>(base_value);
  inner_domain->project_on_vars(*array_value.inner_value, {}, result);
  result = and_exprt(result, segment_elem_equality());
  result = and_exprt(result, map_segments_to_read_indices());
}

/// Try to find ordering among given index expressions.
/// If a unique ordering can be found, orders indices in-situ and returns true,
/// otherwise returns false.
bool array_domaint::order_indices(var_listt &indices, const exprt &array_size)
{
  for(unsigned end = indices.size(); end > 0; --end)
  {
    for(unsigned i = 0; i < end - 1; ++i)
    {
      if(ordered_indices(indices[i + 1], indices[i], array_size))
      {
        const exprt temp = indices[i];
        indices[i] = indices[i + 1];
        indices[i + 1] = temp;
      }
      else if(!ordered_indices(indices[i], indices[i + 1], array_size))
        return false;
    }
  }
  return true;
}

/// Check if there exists an ordering relation <= between two index expressions.
/// Queries SMT solver for negation of the formula:
///   (i1 >= 0 && i1 < size && i2 >= 0 && i2 < size) => i1 <= i2
///
/// If the negation is unsatisfiable, then the formula always holds and there
/// exists an ordering.
bool array_domaint::ordered_indices(const exprt &first,
                                    const exprt &second,
                                    const exprt &array_size)
{
  exprt::operandst bounds = {
    binary_relation_exprt(first, ID_ge, from_integer(0, first.type())),
    binary_relation_exprt(first, ID_lt, array_size),
    binary_relation_exprt(second, ID_ge, from_integer(0, second.type())),
    binary_relation_exprt(second, ID_lt, array_size),
  };
  const exprt ordering_expr = implies_exprt(
    conjunction(bounds), binary_relation_exprt(first, ID_le, second));

  solver->new_context();
  *solver << not_exprt(ordering_expr);
  bool res = false;
  if((*solver)() == decision_proceduret::resultt::D_UNSATISFIABLE)
    res = true;
  solver->pop_context();
  return res;
}

/// Map symbolic indices of segments onto actually read indices.
/// For each segment of an array and for each index read from that array:
///   (idx#read >= lower && idx#read < upper) => idx#read == idx#segment
exprt array_domaint::map_segments_to_read_indices()
{
  exprt::operandst result;
  for(auto &array : segmentation_map)
  {
    auto array_name = get_original_name(to_symbol_expr(array.first));
    auto index_type = array.second.at(0).index_var.type();
    auto &read_indices = SSA.array_index_analysis.read_indices.at(array_name);

    exprt::operandst array_constraint;
    for(auto &read_index_info : read_indices)
    {
      exprt read_index =
        SSA.read_rhs(read_index_info.index, read_index_info.loc);
      if(read_index.type() != index_type)
        read_index = typecast_exprt(read_index, index_type);

      exprt::operandst index_constraint;
      for(auto &segment : array.second)
      {
        index_constraint.push_back(implies_exprt(
          and_exprt(
            binary_relation_exprt(read_index, ID_ge, segment.lower_bound),
            binary_relation_exprt(read_index, ID_lt, segment.upper_bound)),
          equal_exprt(read_index, segment.index_var)));
      }
      array_constraint.push_back(conjunction(index_constraint));
    }
    result.push_back(conjunction(array_constraint));
  }
  return conjunction(result);
}

/// Get conjunction of equalities between segment symbolic variables and
/// corresponding array elements.
exprt array_domaint::segment_elem_equality()
{
  exprt::operandst result;
  // For each segment, add equality:
  //   elem#i = a[idx#i]
  for(auto &array : segmentation_map)
    for(auto &segment : array.second)
      result.push_back(
        equal_exprt(segment.elem_var,
                    index_exprt(segment.array_spec.var, segment.index_var)));
  return conjunction(result);
}

/// Create a new set of variable specifications that contains symbolic element
/// variables of all array segments in the domain.
var_specst array_domaint::var_specs_from_segments()
{
  var_specst var_specs;

  for(auto &array_segments : segmentation_map)
  {
    for(auto &segment : array_segments.second)
    {
      var_spect v;
      v.var = segment.elem_var;
      v.guards = segment.array_spec.guards;
      v.guards.pre_guard =
        and_exprt(v.guards.pre_guard, segment.get_constraint());
      v.guards.post_guard =
        and_exprt(v.guards.post_guard, segment.get_constraint());
      rename(v.guards.post_guard);

      var_specs.push_back(v);
    }
  }

  return var_specs;
}

void array_domaint::output_domain(std::ostream &out, const namespacet &ns) const
{
  inner_domain->output_domain(out, ns);
}

void array_domaint::output_value(std::ostream &out,
                                 const domaint::valuet &value,
                                 const namespacet &ns) const
{
  auto &array_value = dynamic_cast<const array_valuet &>(value);
  inner_domain->output_value(out, *array_value.inner_value, ns);
}

void array_domaint::restrict_to_sympath(const symbolic_patht &sympath)
{
  inner_domain->restrict_to_sympath(sympath);
}

void array_domaint::eliminate_sympaths(
  const std::vector<symbolic_patht> &sympaths)
{
  inner_domain->eliminate_sympaths(sympaths);
}

void array_domaint::undo_sympath_restriction()
{
  inner_domain->undo_sympath_restriction();
}

void array_domaint::remove_all_sympath_restrictions()
{
  inner_domain->undo_sympath_restriction();
}

std::unique_ptr<strategy_solver_baset>
array_domaint::new_strategy_solver(incremental_solvert &solver_,
                                   const local_SSAt &SSA_,
                                   message_handlert &message_handler)
{
  auto inner_solver =
    inner_domain->new_strategy_solver(solver_, SSA_, message_handler);
  return std::unique_ptr<strategy_solver_baset>(new strategy_solver_arrayt(
    *this, std::move(inner_solver), solver_, SSA_, message_handler));
}

/// Get expression for size of an array
/// Currently we support only static arrays
exprt array_domaint::get_array_size(const var_spect &array_spec)
{
  auto &array_type = to_array_type(array_spec.var.type());
  assert(array_type.is_complete());
  exprt size = array_type.size();

  if(array_spec.var.id() == ID_symbol)
    size = SSA.read_rhs(size, array_spec.loc);

  return size;
}

exprt array_domaint::array_segmentt::get_constraint()
{
  const exprt interval_expr =
    and_exprt(binary_relation_exprt(index_var, ID_ge, lower_bound),
              binary_relation_exprt(index_var, ID_lt, upper_bound));
  const exprt bounds_expr = and_exprt(
    binary_relation_exprt(index_var, ID_ge, make_zero(index_var.type())),
    binary_relation_exprt(index_var, ID_lt, array_size));
  const exprt elem_expr =
    equal_exprt(elem_var, index_exprt(array_spec.var, index_var));
  return conjunction(exprt::operandst({bounds_expr, interval_expr, elem_expr}));
}
