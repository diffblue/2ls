/*******************************************************************\

Module: SSA Analyzer

Author: Peter Schrammel

\*******************************************************************/

#ifndef CPROVER_2LS_DOMAINS_SSA_ANALYZER_H
#define CPROVER_2LS_DOMAINS_SSA_ANALYZER_H

#include <util/replace_expr.h>

#include <solver/summary.h>
#include <ssa/local_ssa.h>

#include "strategy_solver_base.h"
#include "template_generator_base.h"

class ssa_analyzert:public messaget
{
public:
  typedef strategy_solver_baset::constraintst constraintst;
  typedef strategy_solver_baset::var_listt var_listt;
  typedef std::vector<std::pair<exprt,std::vector<exprt>>> tmpl_rename_mapt;
  
  ssa_analyzert():
    result(NULL),
    solver_instances(0),
    solver_calls(0)
  {
  }

  ~ssa_analyzert()
  {
    if(result!=NULL)
      delete result;
  }

  void operator()(
    incremental_solvert &solver,
    local_SSAt &SSA,
    const exprt &precondition,
    template_generator_baset &template_generator,
    bool recursive=false,
    std::map<exprt,constant_exprt> context_bounds=
    std::map<exprt,constant_exprt>(),
    tmpl_rename_mapt templ_maps=tmpl_rename_mapt());

  void get_result(exprt &result, const domaint::var_sett &vars);

  void update_heap_out(summaryt::var_sett &out);
  const exprt input_heap_bindings();

  inline unsigned get_number_of_solver_instances() { return solver_instances; }
  inline unsigned get_number_of_solver_calls() { return solver_calls; }

protected:
  domaint *domain; // template generator is responsable for the domain object
  domaint::valuet *result;

  // statistics
  unsigned solver_instances;
  unsigned solver_calls;
};

#endif

