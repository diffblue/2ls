/*******************************************************************\

Module: Generic product combination domain

Author: Viktor Malik

\*******************************************************************/

/// \file
/// Generic product combination domain
/// Can combine arbitrary number of abstract domains side-by-side.
/// Invariant is a conjunction of invariants of individual domains.
/// Designed to work with strategy_solver_productt.

#include "product_domain.h"
#include "strategy_solver_product.h"

void product_domaint::initialize_value(domaint::valuet &_value)
{
  auto &inv=dynamic_cast<valuet &>(_value);
  for(unsigned i=0; i<domains.size(); i++)
    domains[i]->initialize_value(*inv[i]);
}

void product_domaint::output_domain(
  std::ostream &out,
  const namespacet &ns) const
{
  for(auto &domain : domains)
    domain->output_domain(out, ns);
}

void product_domaint::output_value(
  std::ostream &out,
  const domaint::valuet &_value,
  const namespacet &ns) const
{
  auto &inv=dynamic_cast<const valuet &>(_value);
  for(unsigned i=0; i<domains.size(); i++)
    domains[i]->output_value(out, *inv[i], ns);
}

/// Project onto a set of variables. The overall invariant is a conjunction of
/// invariants of inner domains.
void product_domaint::project_on_vars(
  domaint::valuet &_value,
  const var_sett &vars,
  exprt &result)
{
  auto &inv=dynamic_cast<valuet &>(_value);
  exprt::operandst c;
  for(unsigned i=0; i<domains.size(); i++)
  {
    exprt domain_result;
    domains[i]->project_on_vars(*inv[i], vars, domain_result);
    c.push_back(domain_result);
  }
  result=conjunction(c);
}

void product_domaint::restrict_to_sympath(const symbolic_patht &sympath)
{
  for(auto &domain : domains)
    domain->restrict_to_sympath(sympath);
}

void product_domaint::eliminate_sympaths(
  const std::vector<symbolic_patht> &sympaths)
{
  for(auto &domain : domains)
    domain->eliminate_sympaths(sympaths);
}

void product_domaint::undo_sympath_restriction()
{
  for(auto &domain : domains)
    domain->undo_sympath_restriction();
}

void product_domaint::remove_all_sympath_restrictions()
{
  for(auto &domain : domains)
    domain->remove_all_sympath_restrictions();
}

std::unique_ptr<strategy_solver_baset> product_domaint::new_strategy_solver(
  incremental_solvert &solver,
  const local_SSAt &SSA,
  message_handlert &message_handler)
{
  solver_vect solvers;
  for(auto &d : domains)
    solvers.push_back(
      d->new_strategy_solver(solver, SSA, message_handler));
  return std::unique_ptr<strategy_solver_baset>(
    new strategy_solver_productt(
      *this, std::move(solvers), solver, SSA, message_handler));
}

tpolyhedra_domaint *product_domaint::get_tpolyhedra_domain()
{
  tpolyhedra_domaint *domain;
  for(auto &d : domains)
  {
    if((domain = d->get_tpolyhedra_domain()))
      return domain;
  }
  return nullptr;
}
