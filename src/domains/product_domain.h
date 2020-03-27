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

class product_domaint:public domaint
{
public:
  product_domaint(
    unsigned int domainNumber,
    replace_mapt &renamingMap,
    const namespacet &ns,
    const std::vector<domaint *> &domains):
    domaint(domainNumber, renamingMap, ns), domains(domains) {}

  // The domain owns the inner domains, therefore it must delete them properly
  ~product_domaint() override
  {
    for(auto &domain : domains)
      delete domain;
  }

  /// Abstract value is a vector of abstract values of inner domains.
  /// The order has to match the order of domains.
  struct valuet:domaint::valuet, std::vector<domaint::valuet *>
  {
    using std::vector<domaint::valuet *>::vector;

    valuet *clone() override
    {
      auto new_value=new valuet();
      for(const auto &val : *this)
        new_value->push_back(val->clone());
      return new_value;
    }

    // The value owns the inner values and therefore has to delete them
    ~valuet() override
    {
      for(auto &val : *this)
        delete val;
    };
  };

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

  // Product domain contains a vector of domains
  std::vector<domaint *> domains;

  // Value is a vector of values in corresponding domains
  valuet value;
};

#endif // CPROVER_2LS_DOMAINS_PRODUCT_DOMAIN_H
