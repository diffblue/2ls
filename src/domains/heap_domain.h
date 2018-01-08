/*******************************************************************\

Module: Abstract domain for representing heap

Author: Viktor Malik

\*******************************************************************/
#ifndef CPROVER_2LS_DOMAINS_HEAP_DOMAIN_H
#define CPROVER_2LS_DOMAINS_HEAP_DOMAIN_H

#include <memory>

#include <util/namespace.h>
#include <util/message.h>

#include <ssa/local_ssa.h>

#include "domain.h"
#include "template_generator_base.h"

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
    const namespacet &_ns):
    domaint(_domain_number, _renaming_map, _ns)
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
  Base class for a value of a memory configuration
  \*******************************************************************/
  struct row_configt
  {
    // Row is nondeterministic - row expression is TRUE
    bool nondet=false;

    virtual exprt get_row_config_expr(
      const vart &templ_expr,
      bool rename_templ_expr) const=0;

    virtual bool empty() const=0;

    virtual bool add_points_to(const exprt &dest)=0;

    virtual ~row_configt() {}
  };

  /*******************************************************************\
  Stack row configuration - used for pointer-typed stack objects (variables).
  Configuration is a set of objects that the pointer can point to.
  \*******************************************************************/
  struct stack_row_configt:public row_configt
  {
    // Set of objects (or NULL) the row variable can point to
    std::set<exprt> points_to;

    virtual exprt get_row_config_expr(
      const vart &templ_expr,
      bool rename_templ_expr) const override;

    virtual bool add_points_to(const exprt &expr) override;

    virtual bool empty() const override
    {
      return points_to.empty();
    }
  };

  /*******************************************************************\
  Heap row configuration - used for pointer-typed fields of dynamic objects.

  Configuration is a disjunction of conjunctions of paths leading from
  the dynamic object via the field.
  \*******************************************************************/
  struct heap_row_configt:public row_configt
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

    // Dynamic obejct corresponding to the row (contains both object and field)
    dyn_objt dyn_obj;
    // Self link on an abstract dynamic object
    bool self_linkage=false;

    explicit heap_row_configt(const dyn_objt &dyn_obj_):dyn_obj(dyn_obj_) {}

    virtual exprt get_row_config_expr(
      const vart &templ_expr_,
      bool rename_templ_expr) const override;

    virtual bool add_points_to(const exprt &dest) override;

    virtual bool empty() const override
    {
      return paths.empty() && !self_linkage;
    }

    bool add_path(const exprt &dest, const dyn_objt &dyn_obj);

    bool add_all_paths(
      const heap_row_configt &other_config,
      const dyn_objt &dyn_obj);

    bool add_pointed_by(const rowt &row);

    bool add_self_linkage();

  protected:
    static exprt rename_outheap(const symbol_exprt &expr);
  };

  /*******************************************************************\
  Row value is a disjunction of configurations.
  \*******************************************************************/
  struct row_valuet
  {
    mem_kindt mem_kind;
    dyn_objt dyn_obj;

    // Each configuration belongs to a specific symbolic path in program whose
    // execution lead to the given configuration.
    // Path is a conjunction of guards - hence an expression
    std::map<const exprt, std::unique_ptr<row_configt>> configurations;

    row_valuet(const mem_kindt &mem_kind, const dyn_objt &dyn_obj):
      mem_kind(mem_kind), dyn_obj(dyn_obj) {}

    // Allow move constructor only
    row_valuet(const row_valuet &)=delete;
    row_valuet(row_valuet &&)=default;

    row_configt &get_config(const exprt &sym_path);
    stack_row_configt &get_stack_config(const exprt &sym_path);
    heap_row_configt &get_heap_config(const exprt &sym_path);

    // Row manipulation functions
    bool add_points_to(const exprt &sym_path, const exprt &dest);
    bool set_nondet(const exprt &sym_path);

    // Row status functions
    bool empty() const;
    bool is_nondet(const exprt &sym_path);

    exprt get_row_expr(const exprt &templ_expr, bool rename_templ_expr) const;
  };

  // Heap value is a conjunction of rows
  class heap_valuet:
    public valuet,
    public std::vector<row_valuet>
  {
  };

  // Initialize value and domain
  virtual void initialize(valuet &value) override;

  void initialize_domain(
    const local_SSAt &SSA,
    const exprt &precondition,
    template_generator_baset &template_generator);

  // Value -> constraints
  exprt to_pre_constraints(const heap_valuet &value) const;

  void make_not_post_constraints(
    const heap_valuet &value,
    exprt::operandst &cond_exprs,
    exprt::operandst &value_exprs);

  // Row -> constraints
  exprt get_row_pre_constraint(
    const rowt &row,
    const row_valuet &row_value) const;

  exprt get_row_post_constraint(const rowt &row, const row_valuet &row_value);

  // Row modifications
  bool add_transitivity(
    const exprt &sym_path,
    const rowt &from,
    const rowt &to,
    heap_valuet &value);

  bool add_points_to(
    const rowt &row,
    heap_valuet &value,
    const exprt &sym_path,
    const exprt &dest);

  bool set_nondet(
    const rowt &row,
    heap_valuet &value,
    const exprt &sym_path);

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


  void add_new_heap_row_spec(
    const symbol_exprt &expr,
    const unsigned location_number,
    const exprt &post_guard);

  // Utility functions
  static int get_symbol_loc(const exprt &expr);

  friend class strategy_solver_heapt;
};

#endif // CPROVER_2LS_DOMAINS_HEAP_DOMAIN_H
