/**
 * Strategy solver for heap verification.
 *  Viktor Malik, 12.8.2016 (c).
 */
#ifndef CPROVER_STRATEGY_SOLVER_HEAP_H
#define CPROVER_STRATEGY_SOLVER_HEAP_H

#include "../ssa/local_ssa.h"
#include "strategy_solver_base.h"
#include "heap_domain.h"

class strategy_solver_heapt : public strategy_solver_baset
{
 public:
  explicit strategy_solver_heapt(heap_domaint &_heap_domain, incremental_solvert &_solver,
                                   const local_SSAt &SSA, const exprt &precondition)
      : strategy_solver_baset(_solver, SSA.ns), heap_domain(_heap_domain)
  {
    initialize(SSA, precondition);
  }

  virtual bool iterate(invariantt &_inv) override;

  void initialize(const local_SSAt &SSA, const exprt &precondition);

 protected:
  heap_domaint &heap_domain;
  std::set<unsigned> updated_rows;

  int find_member_row(const exprt &obj, const irep_idt &member, int actual_loc,
                      const domaint::kindt &kind);

  bool update_rows_rec(const heap_domaint::rowt &row, heap_domaint::heap_valuet &value);

  void print_solver_expr(const exprt &expr);

  void create_precondition(const symbol_exprt &var, const exprt &precondition,
                           exprt::operandst &equs);

  bool has_precondition_rec(const exprt &expr, const exprt &precondition);
};


#endif //CPROVER_STRATEGY_SOLVER_HEAP_H
