/*******************************************************************\

Module: Generic strategy solver for product combination domains

Author: Viktor Malik

\*******************************************************************/

/// \file
/// Generic strategy solver for product combination domains
/// The strategy solver infers invariants for multiple domains in parallel
/// (domains are side-by-side). Iteration of each domain is run in the context
/// of candidate invariants already inferred in all other domains.

#include "strategy_solver_product.h"

bool strategy_solver_productt::iterate(
  strategy_solver_baset::invariantt &_inv)
{
  auto &inv=dynamic_cast<product_domaint::valuet &>(_inv);

  bool improved=false;
  for(unsigned i=0; i<domain.domains.size(); i++)
  {
    // If the current inner solver symbolic path does not match the current
    // symbolic path (i.e. the current symbolic path changed in this iteration),
    // restrict the current inner domain to the new symbolic path.
    bool new_sympath=false;
    if(with_sympaths &&
       solvers[i]->symbolic_path.get_expr()!=symbolic_path.get_expr())
    {
      new_sympath=true;
      solvers[i]->symbolic_path=symbolic_path;
      domain.domains[i]->restrict_to_sympath(symbolic_path);
    }

    solver.new_context();
    // Get context from all domains except the current one
    for(unsigned j=0; j<domain.domains.size(); j++)
    {
      if(i==j)
        continue;

      exprt domain_context;
      // Calling project_on_vars without the variable set gives the whole
      // (candidate) invariant.
      domain.domains[j]->project_on_vars(*inv[j], {}, domain_context);
      solver << domain_context;
#ifdef DEBUG
      std::cerr << "Context for domain " << j << ": " << std::endl;
      debug_smt_model(domain_context, ns);
#endif
    }

    // Run one iteration of strategy solving for the current domain
    if(solvers[i]->iterate(*inv[i]))
    {
      improved=true;
      // The symbolic path used in the first domain that was improved must be
      // used for the rest of the domains.
      if(with_sympaths && !solvers[i]->symbolic_path.empty() &&
         solvers[i]->symbolic_path!=symbolic_path)
      {
        symbolic_path=solvers[i]->symbolic_path;
      }
    }

    // If a symbolic path restriction was done above for this domain, undo it.
    if(new_sympath)
      domain.domains[i]->undo_sympath_restriction();
    solver.pop_context();
  }

  return improved;
}

void strategy_solver_productt::use_sympaths()
{
  strategy_solver_baset::use_sympaths();
  for(auto &solver : solvers)
    solver->use_sympaths();
}

void strategy_solver_productt::set_sympath(const symbolic_patht &sympath)
{
  strategy_solver_baset::set_sympath(sympath);
  for(auto &solver : solvers)
    solver->set_sympath(sympath);
}

void strategy_solver_productt::clear_symbolic_path()
{
  strategy_solver_baset::clear_symbolic_path();
  for(auto &solver : solvers)
    solver->clear_symbolic_path();
}
