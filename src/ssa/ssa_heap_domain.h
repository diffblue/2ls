/*******************************************************************\

Module: Dynamic objects analysis

Author: Viktor Malik

\*******************************************************************/

/// \file
/// Dynamic objects analysis

#ifndef CPROVER_2LS_SSA_SSA_HEAP_DOMAIN_H
#define CPROVER_2LS_SSA_SSA_HEAP_DOMAIN_H

#define USE_DEPRECATED_STATIC_ANALYSIS_H

#include <analyses/static_analysis.h>

class ssa_heap_domaint:public domain_baset
{
public:
  virtual void transform(
    const namespacet &ns,
    locationt from,
    locationt to) override;
  bool merge(const ssa_heap_domaint &, locationt);

  irep_idt function;

  typedef std::set<exprt> objectst;
  std::map<exprt, objectst> value_map;

  const std::set<symbol_exprt> value(const exprt &expr) const;

  class function_infot
  {
  public:
    std::map<symbol_exprt, std::set<exprt> > new_objects;
    std::set<exprt> modified_objects;
    std::vector<irep_idt> params;

    const exprt corresponding_expr(
      const exprt &expr,
      const code_function_callt::argumentst &arguments,
      unsigned deref_level) const;

  protected:
    const exprt apply_deref(const exprt &expr, unsigned level) const;
  };

  std::map<irep_idt, function_infot> function_map;

  const std::list<symbol_exprt> new_objects() const;
  const std::list<symbol_exprt> new_objects(const irep_idt &fname) const;
  const std::list<symbol_exprt>
  new_caller_objects(const irep_idt &fname, locationt loc) const;

  const std::set<exprt> modified_objects(const irep_idt &fname) const;
protected:
  void assign_lhs_rec(const exprt &lhs, const exprt &rhs, const namespacet &ns);

  void assign_rhs(
    const exprt &rhs,
    const irep_idt &function,
    objectst &objects,
    const namespacet &ns);

  bool is_function_output(
    const exprt &expr,
    const irep_idt &function,
    const namespacet &ns,
    bool in_deref);

  void rename_to_caller(
    symbol_exprt &object,
    locationt loc,
    unsigned &index) const;

  void update_modified(const exprt &expr, const namespacet &ns);
};

class ssa_heap_analysist:public static_analysist<ssa_heap_domaint>
{
public:
  explicit ssa_heap_analysist(const namespacet &_ns):
    static_analysist(_ns) {}

  virtual void initialize(const goto_functionst &goto_functions) override;

protected:
  void init_ptr_param(const exprt &expr, ssa_heap_domaint &f_entry);
};


#endif // CPROVER_2LS_SSA_SSA_HEAP_DOMAIN_H
