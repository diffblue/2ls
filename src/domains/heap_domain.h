/**
 * Abstract domain for representing heap.
 *
 *  Viktor Malik, 12.8.2016 (c).
 */
#ifndef CPROVER_2LS_DOMAINS_HEAP_DOMAIN_H
#define CPROVER_2LS_DOMAINS_HEAP_DOMAIN_H

#include "domain.h"

class heap_domaint:public domaint
{
 public:
  typedef unsigned rowt;
  typedef vart member_fieldt;
  typedef std::pair<exprt, member_fieldt> dyn_objt;

  heap_domaint(
    unsigned int _domain_number,
    replace_mapt &_renaming_map,
    const var_specst &var_specs,
    const namespacet &ns_):
    domaint(_domain_number, _renaming_map, ns_)
  {
    make_template(var_specs, ns_);
  }

  /**
   * Value of a row is set of paths in the heap leading from row variable
   */
  struct row_valuet
  {
    /**
     * Path in a heap. Contains:
     *   - destination object
     *   - set of dynamic objects - this is the set of ssa objects that the path is composed of
     *   - boolean value expressing whether path can have zero length
     *  Paths are ordered by destination only as it is unique within a value row.
     */
    struct patht
    {
      exprt destination;
      mutable std::set<dyn_objt> dyn_objects;

      patht(const exprt &dest_) : destination(dest_) {}

      patht(const exprt &dest_, const std::set<dyn_objt> &dyn_objs_)
          : destination(dest_), dyn_objects(dyn_objs_) {}

      bool operator<(const patht &rhs) const
      {
        return destination < rhs.destination;
      }

      bool operator==(const patht &rhs) const
      {
        return destination == rhs.destination;
      }
    };

    std::set<patht> paths;          /**< Set of paths leading from the row variable */
    std::set<dyn_objt> points_to;   /**< Set of objects (or NULL) the row variable can point to */
    std::set<unsigned> pointed_by;  /**< Set of rows whose variables point to this row */

    /**
     * Get expression for the row value. It is a conjunction of points to expression and path
     * expressions.
     * Points to expression is disjunction of equalities:
     * p = &o (NULL)   for each object 'o' (or NULL) from points_to set
     * Expression of path leading from variable 'p' to destination 'd' via field 'm' and
     * passing through set of objects 'O' has form:
     * p = d ||                            if path can have zero length
     * p = &o && (o.m = d || o.m = o')     where o,o' belong to O and p can point to &o
     * @param templ_expr Pointer variable of the template row
     * @return Row value expression in the described form
     */
    exprt get_row_expr(const vart &templ_expr) const
    {
      if (paths.empty() && points_to.empty()) return false_exprt();
      exprt::operandst result;

      if (!points_to.empty())
      { // Points to expression
        exprt::operandst pt_expr;
        for (auto &pt : points_to)
        {
          exprt lhs = templ_expr;
          pt_expr.push_back(equal_exprt(templ_expr,
                                        is_null_ptr(pt.first) ?
                                        pt.first : address_of_exprt(pt.first)));
        }
        result.push_back(disjunction(pt_expr));
      }

      for (auto &path : paths)
      { // path(p, m, d)[O]
        const exprt &dest = path.destination;
        exprt::operandst path_expr;

        for (const dyn_objt &obj1 : points_to)
        {
          if (path.dyn_objects.find(obj1) != path.dyn_objects.end())
          {
            // p = &o
            exprt equ_exprt = equal_exprt(templ_expr, address_of_exprt(obj1.first));

            exprt::operandst step_expr;
            exprt member_expr = obj1.second;
            // o.m = d
            step_expr.push_back(equal_exprt(member_expr, dest));

            for (auto &obj2 : path.dyn_objects)
            { // o.m = o'
              step_expr.push_back(equal_exprt(member_expr, address_of_exprt(obj2.first)));
            }

            path_expr.push_back(and_exprt(equ_exprt, disjunction(step_expr)));
          }
          else
          {
            path_expr.push_back(equal_exprt(templ_expr,
                                            is_null_ptr(obj1.first) ?
                                            obj1.first : address_of_exprt(obj1.first)));
          }
        }

        result.push_back(disjunction(path_expr));
      }

      return conjunction(result);
    }

    inline bool empty() const
    {
      return paths.empty();
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
    irep_idt member;
    exprt aux_expr;
    kindt kind;
    exprt dyn_obj;
    bool dynamic;
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

  // Add new predicates to a row value (path, or points_to)
  bool add_row_path(const rowt &row, heap_valuet &value, const exprt &dest,
                    const dyn_objt &dyn_obj);

  bool add_all_paths(const rowt &to, const rowt &from, heap_valuet &value, const dyn_objt &dyn_obj);

  bool add_points_to(const rowt &row, heap_valuet &value, const dyn_objt &dyn_obj);

  void add_pointed_by_row(const rowt &row, const rowt &pb_row, heap_valuet &value);

  // Printing
  virtual void output_value(std::ostream &out, const valuet &value,
                            const namespacet &ns) const override;

  virtual void output_domain(std::ostream &out, const namespacet &ns) const override;

  // Projection
  virtual void project_on_vars(valuet &value, const var_sett &vars, exprt &result) override;

  // Conversion of solver value to expression
  static exprt value_to_ptr_exprt(const exprt &expr);

  // Join of values
  virtual void join(valuet &value1, const valuet &value2) override;

  static bool is_null_ptr(const exprt &expr);

 protected:
  templatet templ;

  void make_template(const var_specst &var_specs, const namespacet &ns);

  // Utility functions
  static int get_symbol_loc(const exprt &expr);

  static std::string get_base_name(const exprt &expr);

  friend class strategy_solver_heapt;
};


#endif // CPROVER_2LS_DOMAINS_HEAP_DOMAIN_H
