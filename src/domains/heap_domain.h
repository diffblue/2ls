/**
 * Abstract domain for representing heap.
 *
 *  Viktor Malik, 12.8.2016 (c).
 */
#ifndef CPROVER_HEAP_DOMAIN_H
#define CPROVER_HEAP_DOMAIN_H

#include <util/namespace.h>
#include "domain.h"

class heap_domaint : public domaint
{
 public:
  typedef unsigned rowt;

  heap_domaint(unsigned int _domain_number, replace_mapt &_renaming_map,
               const var_specst &var_specs,
               const namespacet &ns_)
      : domaint(_domain_number, _renaming_map), ns(ns_)
  {
    make_template(var_specs, ns);
  }

  /**
   * Value of a row is set of addresses reachable from pointer (corresponding to template row) via
   * field 'next'.
   */
  struct row_valuet
  {
    std::set<exprt> dests;

    /**
     * Get expression for the row value. The expression has form of disjuncion of equalities.
     * Equality can be:
     *   (templ_expr == NULL)       when pointer is NULL
     *   (templ_expr->next == dest) when pointer points to dest via 'next' field
     * @param templ_expr Pointer variable of the template row
     * @param ns Namespace
     * @return Expression corresponding to value - disjunction of equalities.
     */
    exprt get_row_expr(const vart &templ_expr, const namespacet &ns) const
    {
      exprt::operandst dis;
      for (auto dest : dests)
      {
        if (dest.id() == ID_constant && to_constant_expr(dest).get_value() == ID_NULL)
          dis.push_back(equal_exprt(templ_expr, dest));
        else
        {
          assert(templ_expr.type().id() == ID_pointer);
          const typet &struct_type = templ_expr.type().subtype();
          dis.push_back(
              equal_exprt(member_exprt(dereference_exprt(templ_expr, struct_type),
                                       "next",
                                       dest.type()),
                          dest));
        }
      }
      return disjunction(dis);
    }
  };

  class heap_valuet : public valuet, public std::vector<row_valuet>
  {
  };

  struct template_rowt
  {
    guardt pre_guard;
    guardt post_guard;
    vart expr;
    exprt aux_expr;
    kindt kind;
  };
  typedef std::vector<template_rowt> templatet;

  // Initialize value
  virtual void initialize(valuet &value) override;

  // Value -> constraints
  exprt to_pre_constraints(const heap_valuet &value) const;

  void make_not_post_constraints(const heap_valuet &value, exprt::operandst &cond_exprs,
                                 exprt::operandst &value_exprs);

  // Row -> constraints
  exprt get_row_pre_constraint(const rowt &row, const row_valuet &row_value) const;

  exprt get_row_post_constraint(const rowt &row, const row_valuet &row_value);

  // Add new destination to a row
  bool add_row_dest(const rowt &row, heap_valuet &value, const exprt &dest);

  // Printing
  virtual void output_value(std::ostream &out, const valuet &value,
                            const namespacet &ns) const override;

  virtual void output_domain(std::ostream &out, const namespacet &ns) const override;

  // Projection
  virtual void project_on_vars(valuet &value, const var_sett &vars, exprt &result) override;

  // Conversion of solver value to expression
  static exprt value_to_ptr_exprt(const exprt &expr);

 protected:
  templatet templ;
  namespacet ns;

  void make_template(const var_specst &var_specs, const namespacet &ns);

  friend class strategy_solver_heapt;
};


#endif //CPROVER_HEAP_DOMAIN_H
