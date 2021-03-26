/*******************************************************************\

Module: Generic strategy solver for domain with symbolic paths

Author: Viktor Malik

\*******************************************************************/

/// \file
/// Generic strategy solver for domain with symbolic paths

#include "strategy_solver_sympath.h"

bool strategy_solver_sympatht::iterate(
  strategy_solver_baset::invariantt &_inv)
{
  auto &inv=dynamic_cast<sympath_domaint::sympath_valuet &>(_inv);

  bool improved;
  if(!new_path)
  {
    // Computing invariant for the same symbolic path

#ifdef DEBUG
    std::cerr << "------------------------------------------\n";
    std::cerr << "Same path\n";
    std::cerr << from_expr(ns, "", symbolic_path.get_expr()) << "\n";
#endif

    const exprt sympath=symbolic_path.get_expr();

    inner_solver->set_sympath(symbolic_path);
    domain.inner_domain->restrict_to_sympath(symbolic_path);
    improved=inner_solver->iterate(*inv.at(sympath));
    if(!improved)
    {
      // Invariant for the current symbolic path cannot be improved

#ifdef DEBUG
      std::cerr << "End of path\n";
      std::cerr << "++++++++++++++++++++++++++++++++++++++++++\n";
#endif

      // Check if the computed path is really feasible
      if(!is_current_path_feasible(inv))
        inv.erase(sympath);

      visited_paths.push_back(symbolic_path);
      domain.inner_domain->remove_all_sympath_restrictions();
      domain.inner_domain->eliminate_sympaths(visited_paths);
      clear_symbolic_path();
      improved=true;
      new_path=true;
    }
    else if(inner_solver->symbolic_path.get_expr()!=sympath)
    {
      // The path has been altered during computation (solver has found another
      // loop-select guard that can be true
      auto new_sympath=inner_solver->symbolic_path.get_expr();
      inv.emplace(new_sympath, std::move(inv.at(sympath)));
      inv.erase(sympath);
      symbolic_path=inner_solver->symbolic_path;
#ifdef DEBUG
      std::cerr << "Path altered\n";
      std::cerr << from_expr(ns, "", symbolic_path.get_expr()) << "\n";
#endif
    }
    domain.inner_domain->undo_sympath_restriction();
  }
  else
  {
    // Computing invariant for a new path
    auto new_value=std::unique_ptr<domaint::valuet>(
      inv.inner_value_template->clone());
    domain.inner_domain->initialize_value(*new_value);
    improved=inner_solver->iterate(*new_value);

    if(improved)
    {
      symbolic_path=inner_solver->symbolic_path;
#ifdef DEBUG
      std::cerr << "Symbolic path:\n";
      std::cerr << from_expr(ns, "", symbolic_path.get_expr()) << "\n";
#endif
      const exprt sympath=inner_solver->symbolic_path.get_expr();
      inv.emplace(sympath, std::move(new_value));
      new_path=false;
    }
  }
  return improved;
}

void strategy_solver_sympatht::clear_symbolic_path()
{
  strategy_solver_baset::clear_symbolic_path();
  inner_solver->clear_symbolic_path();
}

/// Check if the current symbolic path is feasible while the computed invariant
/// holds. A path is reachable iff: - for each loop whose loop-select guard
/// occurs in positive form, if its loop head is reachable, then also loop end
/// must be reachable (g#lb => g#le must be SAT) - for each loop whose loop-
/// select guard occurs in negative form, if its loop head is reachable, then
/// its end is not reachable (g#lb => !g#le must be SAT)
bool strategy_solver_sympatht::is_current_path_feasible(
  sympath_domaint::sympath_valuet &value)
{
  bool result=true;
  auto sympath=symbolic_path.get_expr();
  solver.new_context();

  // Path invariant
  exprt invariant;
  domain.inner_domain->project_on_vars(
    *value.at(sympath), {}, invariant);
  solver << invariant;

  for(auto &guard : symbolic_path.path_map)
  {
    // Build condition of reachability of current loop
    exprt loop_cond=loop_conds_map.at(guard.first);
    if(!guard.second)
      loop_cond.op1()=not_exprt(loop_cond.op1());

    solver.new_context();

    // Push states of other loop select gurads and condition of reachablility
    // of the current loop
    const exprt sympath_no_current=symbolic_path.get_expr(guard.first, true);
    solver << sympath_no_current;
    solver << loop_cond;

    // If loop is not reachable in the current context of computed summary,
    // the path is infeasible
    if(solver()==decision_proceduret::resultt::D_UNSATISFIABLE)
      result=false;

    solver.pop_context();
  }

  solver.pop_context();
  return result;
}

void strategy_solver_sympatht::build_loop_conds_map(
  const local_SSAt &SSA)
{
  for(auto &node : SSA.nodes)
  {
    if(node.loophead!=SSA.nodes.end())
    {
      const exprt ls_guard=
        SSA.name(SSA.guard_symbol(), local_SSAt::LOOP_SELECT, node.location);
      const exprt lb_guard=SSA.guard_symbol(node.loophead->location);
      const exprt le_guard=SSA.guard_symbol(node.location);
      loop_conds_map.emplace(ls_guard, and_exprt(lb_guard, le_guard));
    }
  }
}
