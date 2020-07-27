/*******************************************************************\

Module: Generic product combination domain

Author: Viktor Malik

\*******************************************************************/

/// \file
/// Generic product combination domain
/// Can combine arbitrary number of abstract domains side-by-side.
/// Invariant is a conjunction of invariants of individual domains.
/// Designed to work with strategy_solver_productt.

#ifndef CPROVER_2LS_DOMAINS_PRODUCT_DOMAIN_H
#define CPROVER_2LS_DOMAINS_PRODUCT_DOMAIN_H

#include "domain.h"
#include "strategy_solver_base.h"
#include <memory>

typedef std::vector<std::unique_ptr<domaint>> domain_vect;
typedef std::vector<std::unique_ptr<domaint::valuet>> value_vect;

class product_domaint:public domaint
{
public:
  product_domaint(
    unsigned int domainNumber,
    replace_mapt &renamingMap,
    const namespacet &ns,
    domain_vect domains):
    domaint(domainNumber, renamingMap, ns), domains(std::move(domains)) {}

  /// Abstract value is a vector of abstract values of inner domains.
  /// The order has to match the order of domains.
  struct valuet:domaint::valuet, value_vect
  {
    valuet()=default;
    explicit valuet(value_vect values):vector(std::move(values)) {}

    valuet *clone() override
    {
      auto new_value=new valuet();
      for(const auto &val : *this)
        new_value->emplace_back(val->clone());
      return new_value;
    }
  };

  std::unique_ptr<domaint::valuet> new_value() override
  {
    value_vect values;
    for(auto &d : domains)
      values.push_back(std::move(d->new_value()));
    return std::unique_ptr<valuet>(new valuet(std::move(values)));
  }

  // Most of the domain methods are implemented in such way that the
  // corresponding method is called for each domain.

  void initialize_value(domaint::valuet &value) override;
  void output_domain(std::ostream &out, const namespacet &ns) const override;

  void output_value(
    std::ostream &out,
    const domaint::valuet &value,
    const namespacet &ns) const override;

  void project_on_vars(
    domaint::valuet &value,
    const var_sett &vars,
    exprt &result) override;

  void restrict_to_sympath(const symbolic_patht &sympath) override;
  void eliminate_sympaths(const std::vector<symbolic_patht> &sympaths) override;
  void undo_sympath_restriction() override;
  void remove_all_sympath_restrictions() override;

  /// Get a vector of raw pointers to the inner domains
  std::vector<domaint *> get_domains()
  {
    std::vector<domaint *> result;
    for(auto &d : domains)
      result.push_back(d.get());
    return result;
  }

  std::unique_ptr<strategy_solver_baset> new_strategy_solver(
    incremental_solvert &solver,
    const local_SSAt &SSA,
    message_handlert &message_handler) override;

  // Product domain contains a vector of domains
  domain_vect domains;

  // Value is a vector of values in corresponding domains
  valuet value;
};

#endif // CPROVER_2LS_DOMAINS_PRODUCT_DOMAIN_H
