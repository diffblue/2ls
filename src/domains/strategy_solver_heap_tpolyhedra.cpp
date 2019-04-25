/*******************************************************************\

Module: Strategy solver for combination of shape and template
        polyhedra domains.

Author: Viktor Malik

\*******************************************************************/

/// \file
/// Strategy solver for combination of shape and template polyhedra domains.

#include "strategy_solver_heap_tpolyhedra.h"

/// Run iteration of each solver separately, but every time in the context of
/// the current invariant found by the other solver. The template polyhedra
/// solving is also restricted to a symbolic path found by the heap solver.
bool strategy_solver_heap_tpolyhedrat::iterate(
  strategy_solver_baset::invariantt &_inv)
{
  heap_tpolyhedra_domaint::heap_tpolyhedra_valuet &inv=
    static_cast<heap_tpolyhedra_domaint::heap_tpolyhedra_valuet &>(_inv);

  // Run one iteration of heap solver in the context of invariant from
  // the template polyhedra solver
  solver.new_context();
  solver << heap_tpolyhedra_domain.polyhedra_domain.to_pre_constraints(
    inv.tpolyhedra_value);
  bool heap_improved=heap_solver.iterate(inv.heap_value);
  solver.pop_context();

  if(heap_improved)
  {
    // If heap part was improved, restrict template polyhedra part to the found
    // symbolic path
    symbolic_path=heap_solver.symbolic_path;
    heap_tpolyhedra_domain.polyhedra_domain.restrict_to_sympath(symbolic_path);
  }

  // Run one interation of the template polyhedra solver in the context of
  // invariant from the heap solver
  solver.new_context();
  solver << heap_tpolyhedra_domain.heap_domain.to_pre_constraints(
    inv.heap_value);
  bool tpolyhedra_improved=tpolyhedra_solver.iterate(inv.tpolyhedra_value);
  solver.pop_context();

  if(heap_improved)
    heap_tpolyhedra_domain.polyhedra_domain.undo_restriction();

  return heap_improved || tpolyhedra_improved;
}

void strategy_solver_heap_tpolyhedrat::set_message_handler(
  message_handlert &_message_handler)
{
  heap_solver.set_message_handler(_message_handler);
  tpolyhedra_solver.set_message_handler(_message_handler);
}

void strategy_solver_heap_tpolyhedrat::clear_symbolic_path()
{
  heap_solver.symbolic_path.clear();
  tpolyhedra_solver.symbolic_path.clear();
}
