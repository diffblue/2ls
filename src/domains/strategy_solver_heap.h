/*******************************************************************\

Module: Strategy solver for heap shape analysis

Author: Viktor Malik

\*******************************************************************/
#ifndef CPROVER_2LS_DOMAINS_STRATEGY_SOLVER_HEAP_H
#define CPROVER_2LS_DOMAINS_STRATEGY_SOLVER_HEAP_H

#include <ssa/local_ssa.h>
#include "strategy_solver_base.h"
#include "heap_domain.h"
#include "template_generator_base.h"

class strategy_solver_heapt:public strategy_solver_baset
{
public:
  strategy_solver_heapt(
    heap_domaint &_heap_domain,
    incremental_solvert &_solver,
    const local_SSAt &SSA,
    const exprt &precondition,
    message_handlert &message_handler,
    template_generator_baset &template_generator):
    strategy_solver_baset(_solver, SSA.ns),
    heap_domain(_heap_domain),
    loop_guards(SSA.loop_guards)
  {
    set_message_handler(message_handler);
    initialize(SSA, precondition, template_generator);
  }

  virtual bool iterate(invariantt &_inv) override;

  void initialize(
    const local_SSAt &SSA,
    const exprt &precondition,
    template_generator_baset &template_generator);

protected:
  heap_domaint &heap_domain;
  std::set<symbol_exprt> loop_guards;
  std::set<unsigned> updated_rows;

  int find_member_row(
    const exprt &obj,
    const irep_idt &member,
    int actual_loc,
    const domaint::kindt &kind);

  bool update_rows_rec(
    const exprt &sym_path,
    const heap_domaint::rowt &row,
    heap_domaint::heap_valuet &value);

  const exprt get_symbolic_path(const heap_domaint::rowt &row);

  void print_solver_expr(const exprt &expr);
};


#endif // CPROVER_2LS_DOMAINS_STRATEGY_SOLVER_HEAP_H
