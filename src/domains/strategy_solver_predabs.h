#ifndef CPROVER_STRATEGY_SOLVER_PREDABS_H
#define CPROVER_STRATEGY_SOLVER_PREDABS_H 

#include "strategy_solver_base.h"
#include "predabs_domain.h"

class strategy_solver_predabst : public strategy_solver_baset
{
 public:
  explicit strategy_solver_predabst(
    predabs_domaint &_predabs_domain,
    incremental_solvert &_solver, 
    const namespacet &_ns) : 
    strategy_solver_baset(_solver, _ns),
    predabs_domain(_predabs_domain)
  {
    predabs_domain.get_row_set(todo_preds);
  }

  virtual bool iterate(invariantt &inv);

 protected:
  predabs_domaint &predabs_domain;

  typedef std::set<unsigned> worklistt;
  worklistt todo_preds;
  worklistt todo_notpreds;


};

#endif
