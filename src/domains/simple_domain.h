/*******************************************************************\

Module: Generic simple abstract domain class

Author: Viktor Malik

\*******************************************************************/

/// \file
/// Generic simple abstract domain class
/// Designed to work with the generic simple strategy solver located in
/// strategy_solver_simplet.
/// Implements a default behaviour for a number of methods that are common for
/// multiple simple abstract domains.

#ifndef CPROVER_2LS_DOMAINS_SIMPLE_DOMAIN_H
#define CPROVER_2LS_DOMAINS_SIMPLE_DOMAIN_H

#include "domain.h"
#include <memory>

class simple_domaint:public domaint
{
public:
  simple_domaint(
    unsigned domain_number,
    replace_mapt &renaming_map,
    const namespacet &ns):
    domaint(domain_number, renaming_map, ns) {}

  typedef unsigned rowt;

  /// Template row expression - defined per-domain
  struct template_row_exprt
  {
    virtual ~template_row_exprt()=default;
    /// Get a vector of expressions used in the row
    virtual std::vector<exprt> get_row_exprs()=0;
    /// Output the template row (with the template row parameters)
    virtual void output(std::ostream &out, const namespacet &ns) const=0;
  };

  /// Template row
  /// Contains a row expression (defined per-domain) and row guards.
  struct template_rowt
  {
    // The expression is defined as unique_ptr to enable polymorphism
    std::unique_ptr<template_row_exprt> expr;
    guardst guards;
  };

  /// Template is a vector of template rows
  struct templatet:std::vector<template_rowt>
  {
    /// Output the domain template
    virtual void output(std::ostream &out, const namespacet &ns) const;
  };

  templatet templ;

  struct valuet:domaint::valuet
  {
    /// Get expression corresponding to the current value of the given template
    /// row parameter.
    virtual exprt get_row_expr(
      rowt row,
      const template_rowt &templ_row) const=0;
  };

  /// Domain should return true if it wants to improve its invariants.
  /// Otherwise no further improvements of invariants is done.
  virtual bool has_something_to_solve() { return true; }

  /// Edit invariant based on the current model of satisfiability.
  /// Every domain should implement this function.
  virtual bool edit_row(const rowt &row, valuet &inv, bool improved)=0;

  /// Get expression that should be made permanent in the SMT solver.
  /// This method is called after each iteration of strategy solver.
  virtual exprt get_permanent_expr(valuet &value) { return true_exprt(); }

  /// Called when the model is unsatisfiable
  /// Returns true if the invariant should be further improved.
  virtual bool handle_unsat(valuet &value, bool improved) { return improved; }

  // Pre- and post- constraints

  /// Get pre constraints from the given value.
  /// Default behaviour: make a conjunction of row pre constraints for each
  /// template row.
  virtual exprt to_pre_constraints(const valuet &value);

  /// Get row pre constraint for the given row from the given abstract value.
  /// Default row pre constraint:
  ///   pre_guard => row_value_expression
  virtual exprt get_row_pre_constraint(rowt row, const valuet &value);

  /// Get post constraints from the given value.
  /// Since it is necessary to know which constraint was satisfied by the SMT
  /// solver, they are stored in a vector cond_exprs and the strategy solver
  /// makes a disjunction of them and passes it to the SMT solver.
  /// Post constraints are typically negations of row expressions (to solve the
  /// "exists forall" problem).
  /// Default behaviour: each template row has its own post constraint.
  virtual void make_not_post_constraints(
    const valuet &value,
    exprt::operandst &cond_exprs);

  /// Get row post constraint for the given row from the given abstract value.
  /// Default post constraint:
  ///   aux_expr && !(post_guard => row_value_expression)
  virtual exprt get_row_post_constraint(rowt row, const valuet &value);

  /// Get value constraint for the given row.
  /// Default is the row expression of the value.
  virtual exprt get_row_value_constraint(rowt row, const valuet &value);

  std::vector<guard_invariant> get_guards_and_invariants(
    const domaint::valuet &value) const override;

  /// Output the domain (its template)
  /// Default behaviour: output template.
  void output_domain(std::ostream &out, const namespacet &ns) const override;

  /// Output the given abstract value in this domain.
  /// Default behavior: for each template row, print the row value expression.
  void output_value(
    std::ostream &out,
    const domaint::valuet &value,
    const namespacet &ns) const override;

  /// Project invariant (abstract value) onto a set of variables.
  /// Default behaviour: result is a conjunction of expressions of all template
  /// row such that all symbols occurring in the row expression are in vars
  /// Here, the projected expression is:
  ///   pre_constraint       for LOOP rows
  ///   value_row_expression for IN and OUT rows
  // (not useful to make value const (e.g. union-find))
  void project_on_vars(
    domaint::valuet &value,
    const var_sett &vars,
    exprt &result) override;

  /// Return the loop guard for the given template row.
  /// By default, it is the second conjunct in the row pre-guard.
  virtual exprt get_current_loop_guard(rowt row);
  /// Restrict the template to the given symbolic path.
  /// Default behaviour: for each template row, add all loop guards from the
  /// symbolic path (except for the loop guard corresponding to the row)
  /// to aux_expr.
  void restrict_to_sympath(const symbolic_patht &sympath) override;
  /// Restrict template to any other paths than those specified.
  void eliminate_sympaths(const std::vector<symbolic_patht> &sympaths) override;
  /// Undo the last symbolic path restriction
  /// Default behaviour: for each template row, remove the second conjunct
  /// from aux_expr.
  void undo_sympath_restriction() override;
  /// Remove all symbolic path restrictions.
  /// Default behaviour: for each template row, clear aux_expr.
  void remove_all_sympath_restrictions() override;

  // returns true as long as further refinements are possible
  virtual void reset_refinements() {}

  virtual bool refine() { return false; }

  std::unique_ptr<strategy_solver_baset> new_strategy_solver(
    incremental_solvert &solver,
    const local_SSAt &SSA,
    message_handlert &message_handler) override;

protected:
  // handles on values to retrieve from model
  // each row has a condition literal and a vector of value expressions
  bvt strategy_cond_literals;
  std::vector<exprt::operandst> strategy_value_exprs;
  // values of value expressions for the current row retrieved from the model
  exprt::operandst smt_model_values;

  friend class strategy_solver_simplet;
};


#endif // CPROVER_2LS_DOMAINS_SIMPLE_DOMAIN_H
