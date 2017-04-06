/**
 * Abstract domain for representing heap.
 *
 *  Viktor Malik, 12.8.2016 (c).
 */
#ifndef CPROVER_2LS_DOMAINS_HEAP_DOMAIN_H
#define CPROVER_2LS_DOMAINS_HEAP_DOMAIN_H

#include <util/message.h>
#include <memory>
#include "../ssa/local_ssa.h"
#include "domain.h"
#include "template_generator_base.h"

class heap_domaint:public domaint
{
 public:
  typedef unsigned rowt;
  typedef vart member_fieldt;
  typedef std::pair<exprt, member_fieldt> dyn_objt;

  typedef enum { STACK, HEAP } mem_kindt;

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
    bool nondet = false;            /**< Row is nondeterministic - expression is TRUE */

    virtual exprt get_row_expr(const vart &templ_expr, bool rename_templ_expr) const = 0;

    virtual bool empty() const = 0;

    virtual bool add_points_to(const exprt &dest) = 0;
  };

  struct stack_row_valuet : public row_valuet
  {
    std::set<exprt> points_to;   /**< Set of objects (or NULL) the row variable can point to */

    virtual exprt get_row_expr(const vart &templ_expr, bool rename_templ_expr) const override;

    virtual bool add_points_to(const exprt &expr) override;

    virtual bool empty() const override
    {
      return points_to.empty();
    }
  };

  struct heap_row_valuet : public row_valuet
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

    typedef std::set<patht> pathsett;

    std::list<pathsett> paths;
    std::set<rowt> pointed_by;      /**< Set of rows whose variables point to this row */
    dyn_objt dyn_obj;
    bool self_linkage = false;

    heap_row_valuet(const dyn_objt &dyn_obj_) : dyn_obj(dyn_obj_) {}

    virtual exprt get_row_expr(const vart &templ_expr_, bool rename_templ_expr) const override;

    virtual bool add_points_to(const exprt &dest) override;

    virtual bool empty() const override
    {
      return paths.empty();
    }

    bool add_path(const exprt &dest, const dyn_objt &dyn_obj);

    bool add_path(const exprt &dest, const heap_domaint::dyn_objt &dyn_obj, pathsett &path_set);

    bool join_path_sets(heap_domaint::heap_row_valuet::pathsett &dest,
                            const heap_domaint::heap_row_valuet::pathsett &src,
                            const dyn_objt &through);

    bool add_all_paths(const heap_row_valuet &other_val, const dyn_objt &dyn_obj);

    bool add_pointed_by(const rowt &row);

    bool add_self_linkage();

   protected:
    static exprt rename_outheap(const symbol_exprt &expr);
  };

  class heap_valuet : public valuet, public std::vector<std::unique_ptr<row_valuet>>
  {
   public:
    row_valuet &operator[](const rowt &row) const
    {
      return *(this->at(row).get());
    }
  };

  struct template_rowt
  {
    vart expr;
    guardt pre_guard;
    guardt post_guard;
    exprt aux_expr;
    kindt kind;
    mem_kindt mem_kind;
    exprt dyn_obj;
    irep_idt member;
  };
  typedef std::vector<template_rowt> templatet;

  // Initialize value
  virtual void initialize(valuet &value) override;

  void initialize_domain(const local_SSAt &SSA, const exprt &precondition,
                         template_generator_baset &template_generator);

  // Value -> constraints
  exprt to_pre_constraints(const heap_valuet &value) const;

  void make_not_post_constraints(const heap_valuet &value, exprt::operandst &cond_exprs,
                                 exprt::operandst &value_exprs);

  // Row -> constraints
  exprt get_row_pre_constraint(const rowt &row, const row_valuet &row_value) const;

  exprt get_row_post_constraint(const rowt &row, const row_valuet &row_value);

  bool add_transitivity(const rowt &from, const rowt &to, heap_valuet &value);

  bool add_points_to(const rowt &row, heap_valuet &value, const exprt &dest);

  bool set_nondet(const rowt &row, heap_valuet &value);

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

  // Getters for protected fields
  const std::list<symbol_exprt> get_new_heap_vars();

  const exprt get_advancer_bindings() const;
  const exprt get_aux_bindings() const;
  const exprt get_input_bindings() const;

 protected:
  templatet templ;

  exprt::operandst advancer_bindings;
  exprt::operandst aux_bindings;

  /**
   * Specification of a new heap row. The row is added dynamically at the beginning of the analysis
   * after binding of iterators to actual dynamic objects from calling context.
   */
  class heap_row_spect
  {
   public:
    symbol_exprt expr;        /**< Row expression */
    unsigned location_number; /**< Location where the corresponding iterator occured */

    mutable exprt post_guard;

    heap_row_spect(const symbol_exprt &expr, unsigned int location_number, const exprt &post_guard)
        : expr(expr), location_number(location_number), post_guard(post_guard) {}

    bool operator<(const heap_row_spect &rhs) const
    {
      return std::tie(expr, location_number) < std::tie(rhs.expr, rhs.location_number);
    }

    bool operator==(const heap_row_spect &rhs) const
    {
      return std::tie(expr, location_number) == std::tie(rhs.expr, rhs.location_number);
    }
  };

  std::set<heap_row_spect> new_heap_row_specs;

  void make_template(const var_specst &var_specs, const namespacet &ns);

  void add_template_row(const var_spect &var_spec, const typet &pointed_type);

  // Initializing functions
  void bind_advancers(const local_SSAt &SSA, const exprt &precondition,
                      template_generator_baset &template_generator);

  void create_precondition(const symbol_exprt &var, const exprt &precondition);

  void new_output_template_row(const symbol_exprt &var, const unsigned location_number,
                               const exprt &post_guard, const local_SSAt &SSA,
                               template_generator_baset &template_generator);

  static std::set<symbol_exprt> reachable_objects(const advancert &advancer,
                                                  const exprt &precondition);

  static std::set<exprt> collect_preconditions_rec(const exprt &expr, const exprt &precondition);

  void add_new_heap_row_spec(const symbol_exprt &expr, const unsigned location_number,
                             const exprt &post_guard);
  // Utility functions
  static int get_symbol_loc(const exprt &expr);

  static std::string get_base_name(const exprt &expr);

  friend class strategy_solver_heapt;
};


#endif // CPROVER_2LS_DOMAINS_HEAP_DOMAIN_H
