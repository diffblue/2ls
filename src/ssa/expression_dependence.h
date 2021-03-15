/*******************************************************************\

Module: Analysis of potential relations among expressions.
        Computes which expressions (mainly symbols) occur in the same
        expression/statement and therefore there may be a relation
        between them. This information can be later used to create
        a more precise analysis template.

Author: Viktor Malik, viktor.malik@gmail.com

\*******************************************************************/

/// \file
/// Analysis of potential relations among expressions.
/// Computes which expressions (mainly symbols) occur in the same
/// expression/statement and therefore there may be a relation between them.
/// This information can be later used to create a more precise analysis
/// template.

#ifndef CPROVER_2LS_SSA_EXPRESSION_DEPENDENCE_H
#define CPROVER_2LS_SSA_EXPRESSION_DEPENDENCE_H

#include <util/threeval.h>
#include <util/union_find.h>

#include <analyses/ai.h>
#include <ssa/local_ssa.h>

class expression_dependence_domaint : public ai_domain_baset
{
public:
  expression_dependence_domaint() : has_values(false)
  {
  }

  // Equivalence partitioning of the expressions onto dependence sets
  union_find<exprt, irep_hash> dep_sets;

  void transform(const irep_idt &,
                 trace_ptrt trace_from,
                 const irep_idt &,
                 trace_ptrt trace_to,
                 ai_baset &ai,
                 const namespacet &ns) override;

  void output(std::ostream &out,
              const ai_baset &ai,
              const namespacet &ns) const override;

  bool merge(const expression_dependence_domaint &other,
             trace_ptrt trace_from,
             trace_ptrt trace_to);

  void make_bottom() override
  {
    dep_sets.clear();
    has_values = tvt(false);
  }

  void make_top() override
  {
    dep_sets.clear();
    has_values = tvt(true);
  }

  void make_entry() override
  {
    make_top();
  }

  bool is_bottom() const override
  {
    return has_values.is_false();
  }

  bool is_top() const override
  {
    return has_values.is_true();
  }

protected:
  void collect_exprs_rec(const exprt &expr,
                         const namespacet &ns,
                         std::set<exprt> &result);
  void make_union(std::set<exprt> &exprs);
  void make_union(std::set<exprt> &exprs1, std::set<exprt> &exprs2);

  static bool may_ignore(const ssa_objectt &ssa_object);

  struct conditionalt
  {
    std::set<exprt> guard_exprs;
    locationt end;

    bool operator==(const conditionalt &rhs) const
    {
      return std::tie(guard_exprs, end) == std::tie(rhs.guard_exprs, rhs.end);
    }
  };
  std::vector<conditionalt> conditionals;

  unsigned loop_end = 0;
  tvt has_values;
};

class expression_dependencet : public ait<expression_dependence_domaint>
{
public:
  expression_dependencet(const irep_idt &function_identifier,
                         const goto_functionst::goto_functiont &goto_function,
                         const local_SSAt &SSA)
    : SSA(SSA)
  {
    operator()(function_identifier, goto_function, SSA.ns);
  }

  const expression_dependence_domaint &
  get_deps_for_ssa_expr(const exprt &expr, const local_SSAt &SSA);

protected:
  void
  initialize(const irep_idt &function_id,
             const goto_functionst::goto_functiont &goto_function) override;

  const local_SSAt &SSA;

  friend class expression_dependence_domaint;
};

#endif //CPROVER_2LS_SSA_EXPRESSION_DEPENDENCE_H
