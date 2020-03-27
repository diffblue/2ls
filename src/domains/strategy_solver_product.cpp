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

  int first_improved=-1;

  bool improved=false;
  for(unsigned i=0; i<domain.domains.size(); i++)
  {
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
      if(first_improved==-1 && i!=domain.domains.size()-1)
      {
        first_improved=i;
        symbolic_path=solvers[i]->symbolic_path;
        for(unsigned j=i+1; j<domain.domains.size(); j++)
        {
          domain.domains[j]->restrict_to_sympath(symbolic_path);
        }
      }
    }
    solver.pop_context();
  }
  if(improved)
  {
    for(unsigned i=first_improved+1; i<domain.domains.size(); i++)
      // Undo symbolic path restriction done above
      domain.domains[i]->undo_sympath_restriction();
  }

  return improved;
}

void strategy_solver_productt::clear_symbolic_path()
{
  for(auto &solver : solvers)
    solver->clear_symbolic_path();
}
