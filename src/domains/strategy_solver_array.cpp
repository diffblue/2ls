/*******************************************************************\

Module: Strategy solver for the array abstract domain

Author: Viktor Malik <viktor.malik@gmail.com>

\*******************************************************************/
/// \file
/// Strategy solver for the array abstract domain
/// The strategy solver infers invariants for array elements (using symbolic
/// element variables) in the inner domain.

#include "strategy_solver_array.h"

bool strategy_solver_arrayt::iterate(strategy_solver_baset::invariantt &_inv)
{
  auto &inv = dynamic_cast<array_domaint::array_valuet &>(_inv);
  solver.new_context();
  // Add bindings for symbolic segment index and element variables
  solver << domain.segment_elem_equality();
  solver << domain.map_segments_to_read_indices();
  // Run iteration in the inner solver
  bool res = inner_solver->iterate(*inv.inner_value);
  solver.pop_context();
  return res;
}

void strategy_solver_arrayt::use_sympaths()
{
  inner_solver->use_sympaths();
}

void strategy_solver_arrayt::set_sympath(const symbolic_patht &sympath)
{
  inner_solver->set_sympath(sympath);
}

void strategy_solver_arrayt::clear_symbolic_path()
{
  inner_solver->clear_symbolic_path();
}
