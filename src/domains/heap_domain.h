/*******************************************************************\

Module: Abstract domain for representing heap

Author: Viktor Malik

\*******************************************************************/
/// \file
/// Abstract domain for representing heap

#ifndef CPROVER_2LS_DOMAINS_HEAP_DOMAIN_H
#define CPROVER_2LS_DOMAINS_HEAP_DOMAIN_H

#include <memory>

#include <util/namespace.h>
#include <util/message.h>

#include <ssa/local_ssa.h>

#include "domain.h"
#include "template_generator_base.h"
#include <ssa/ssa_inliner.h>

class heap_domaint:public domaint
{
public:
  typedef unsigned rowt;
  // Field of a dynamic object (a variable)
  typedef vart member_fieldt;
  // We represent dynamic object by the object itself and its member field
  typedef std::pair<exprt, member_fieldt> dyn_objt;

  typedef enum { STACK, HEAP } mem_kindt;

  heap_domaint(
    unsigned int _domain_number,
    replace_mapt &_renaming_map,
    const var_specst &var_specs,
    const local_SSAt &SSA):
    domaint(_domain_number, _renaming_map, SSA.ns)
  {
    make_template(var_specs, ns);
  }

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

  /*******************************************************************\
  Base class for a value of a row
  \*******************************************************************/
  struct row_valuet
  {
    // Row is nondeterministic - row expression is TRUE
    bool nondet=false;

    const namespacet &ns;

    explicit row_valuet(const namespacet &ns):ns(ns) {}

    virtual exprt get_row_expr(
      const vart &templ_expr,
      bool rename_templ_expr) const=0;

    virtual bool empty() const=0;

    virtual bool add_points_to(const exprt &dest)=0;

    virtual void clear()=0;

    virtual ~row_valuet() {}
  };

  /*******************************************************************\
  Stack row - used for pointer-typed stack objects (variables).
  Value is a set of objects that the pointer can point to.
  \*******************************************************************/
  struct stack_row_valuet:public row_valuet
  {
    // Set of objects (or NULL) the row variable can point to
    std::set<exprt> points_to;

    explicit stack_row_valuet(const namespacet &ns):row_valuet(ns) {}

    virtual exprt get_row_expr(
      const vart &templ_expr,
      bool rename_templ_expr) const override;

    virtual bool add_points_to(const exprt &expr) override;

    virtual bool empty() const override
    {
      return points_to.empty();
    }

    virtual void clear() override;
  };

  /*******************************************************************\
  Heap row - used for pointer-typed fields of dynamic objects.

  Value is a disjunction of conjunctions of paths leading from the dynamic
  object via the field.
  \*******************************************************************/
  struct heap_row_valuet:public row_valuet
  {
    /*******************************************************************\
    Path in a heap. Contains:
      - destination object
      - set of dynamic objects - set of SSA objects that the path is composed of

    Paths are ordered by destination only as it is unique within a value row.
    \*******************************************************************/
    struct patht
    {
      exprt destination;
      mutable std::set<dyn_objt> dyn_objects;

      patht(const exprt &dest_):destination(dest_) {} // NOLINT(*)

      patht(const exprt &dest_, const std::set<dyn_objt> &dyn_objs_):
        destination(dest_), dyn_objects(dyn_objs_) {}

      bool operator<(const patht &rhs) const
      {
        return destination<rhs.destination;
      }

      bool operator==(const patht &rhs) const
      {
        return destination==rhs.destination;
      }
    };

    // Set of paths interpreted as a conjunction of paths
    std::set<patht> paths;

    // Set of rows whose variables point to this row
    std::set<rowt> pointed_by;

    // Dynamic object corresponding to the row (contains both object and field)
    dyn_objt dyn_obj;
    // Self link on an abstract dynamic object
    bool self_linkage=false;

    heap_row_valuet(const namespacet &ns, const dyn_objt &dyn_obj_):
      row_valuet(ns), dyn_obj(dyn_obj_) {}

    virtual exprt get_row_expr(
      const vart &templ_expr_,
      bool rename_templ_expr) const override;

    virtual bool add_points_to(const exprt &dest) override;

    virtual bool empty() const override
    {
      return paths.empty() && !self_linkage;
    }

    virtual void clear() override;

    bool add_path(const exprt &dest, const dyn_objt &dyn_obj);

    bool add_all_paths(
      const heap_row_valuet &other_val,
      const dyn_objt &dyn_obj);

    bool add_pointed_by(const rowt &row);

    bool add_self_linkage();

  protected:
    static exprt rename_outheap(const symbol_exprt &expr);
  };

  // Heap value is a conjunction of rows
  class heap_valuet:
    public valuet,
    public std::vector<std::unique_ptr<row_valuet>>
  {
  public:
    row_valuet &operator[](const rowt &row) const
    {
      return *(this->at(row).get());
    }
  };

  // Initialize value and domain
  virtual void initialize(valuet &value) override;

  void initialize_domain(
    const local_SSAt &SSA,
    const exprt &precondition,
    template_generator_baset &template_generator);

  std::vector<exprt> get_required_smt_values(size_t row);
  void set_smt_values(std::vector<exprt> got_values, size_t row);

  // Value -> constraints
  exprt to_pre_constraints(valuet &_value);

  void make_not_post_constraints(
    valuet &_value,
    exprt::operandst &cond_exprs);

  // Row -> constraints
  exprt get_row_pre_constraint(
    const rowt &row,
    const row_valuet &row_value) const;

  exprt get_row_post_constraint(const rowt &row, const row_valuet &row_value);

  // Row modifications
  bool add_transitivity(const rowt &from, const rowt &to, heap_valuet &value);

  bool add_points_to(const rowt &row, heap_valuet &value, const exprt &dest);

  bool set_nondet(const rowt &row, heap_valuet &value);

  // Printing
  virtual void output_value(
    std::ostream &out,
    const valuet &value,
    const namespacet &ns) const override;

  virtual void output_domain(
    std::ostream &out,
    const namespacet &ns) const override;

  // Projection
  virtual void
  project_on_vars(valuet &value, const var_sett &vars, exprt &result) override;

  // Conversion of solver value to expression
  static exprt value_to_ptr_exprt(const exprt &expr);

  // Join of values
  virtual void join(valuet &value1, const valuet &value2) override;

  // Restriction to symbolic paths
  void restrict_to_sympath(const symbolic_patht &sympath);
  void undo_restriction();
  void eliminate_sympaths(const std::vector<symbolic_patht> &sympaths);
  void clear_aux_symbols();

  // Getters for protected fields
  const std::list<symbol_exprt> get_new_heap_vars();

  exprt get_iterator_bindings() const;
  exprt get_aux_bindings() const;
  exprt get_input_bindings() const;

  bool empty() const
  {
    return templ.empty();
  }

protected:
  templatet templ;

  // Bindings computed during interprocedural analysis
  exprt::operandst iterator_bindings;
  exprt::operandst aux_bindings;

  std::set<unsigned> updated_rows;
  exprt solver_value_op0;
  exprt solver_value_op1;

  /*******************************************************************\
  Specification of a new heap row that is added dynamically
  at the beginning of the analysis, after binding of iterators to the actual
  dynamic objects from the calling context.

  Contains row expression and a location where the corresponding
  iterator occured.
  \*******************************************************************/
  class heap_row_spect
  {
  public:
    symbol_exprt expr;
    unsigned location_number;

    mutable exprt post_guard;

    heap_row_spect(
      const symbol_exprt &expr,
      unsigned location_number,
      const exprt &post_guard):
      expr(expr), location_number(location_number), post_guard(post_guard) {}

    bool operator<(const heap_row_spect &rhs) const
    {
      return std::tie(expr, location_number)<
             std::tie(rhs.expr, rhs.location_number);
    }

    bool operator==(const heap_row_spect &rhs) const
    {
      return std::tie(expr, location_number)==
             std::tie(rhs.expr, rhs.location_number);
    }
  };

  // Set of new heap rows added during analysis (used for interprocedural)
  std::set<heap_row_spect> new_heap_row_specs;

  void make_template(const var_specst &var_specs, const namespacet &ns);

  void add_template_row(const var_spect &var_spec, const typet &pointed_type);
  void add_template_row_pair(
    const var_spect &var_spec1,
    const var_spect &var_spec2,
    const typet &pointed_type);

  // Initializing functions
  void bind_iterators(
    const local_SSAt &SSA,
    const exprt &precondition,
    template_generator_baset &template_generator);

  void create_precondition(const symbol_exprt &var, const exprt &precondition);

  void new_output_template_row(
    const symbol_exprt &var,
    const unsigned location_number,
    const exprt &post_guard,
    const local_SSAt &SSA,
    template_generator_baset &template_generator);

  const exprt iterator_access_bindings(
    const symbol_exprt &src,
    const exprt &init_pointer,
    const symbol_exprt &iterator_sym,
    const std::vector<irep_idt> &fields,
    const list_iteratort::accesst &access,
    const unsigned level,
    exprt::operandst guards,
    const exprt &precondition,
    const local_SSAt &SSA);

  const std::set<symbol_exprt> reachable_objects(
    const exprt &src,
    const std::vector<irep_idt> &fields,
    const exprt &precondition) const;

  static const std::set<exprt> collect_preconditions_rec(
    const exprt &expr,
    const exprt &precondition);

  virtual exprt get_current_loop_guard(size_t row) override;

  bool edit_row(const rowt &row, valuet &inv, bool improved);

  void add_new_heap_row_spec(
    const symbol_exprt &expr,
    const unsigned location_number,
    const exprt &post_guard);

  // Utility functions
  static int get_symbol_loc(const exprt &expr);
  const exprt get_points_to_dest(
    const exprt &solver_value,
    const exprt &templ_row_expr);

  int find_member_row(
    const exprt &obj,
    const irep_idt &member,
    int actual_loc,
    const domaint::kindt &kind);

  bool update_rows_rec(
    const heap_domaint::rowt &row,
    heap_domaint::heap_valuet &value);
  void clear_pointing_rows(
    const heap_domaint::rowt &row,
    heap_domaint::heap_valuet &value);
  const exprt initialize_solver(
    const local_SSAt &SSA,
    const exprt &precondition,
    template_generator_baset &template_generator);

  friend class strategy_solver_heapt;
};

#endif // CPROVER_2LS_DOMAINS_HEAP_DOMAIN_H
