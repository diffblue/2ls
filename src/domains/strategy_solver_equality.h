#ifndef CPROVER_STRATEGY_SOLVER_EQUALITY_H
#define CPROVER_STRATEGY_SOLVER_EQUALITY_H 

#include "strategy_solver_base.h"
#include "equality_domain.h"

class strategy_solver_equalityt : public strategy_solver_baset
{
 public:
  explicit strategy_solver_equalityt(
    const constraintst &program,
    replace_mapt &_renaming_map,
    equality_domaint &_equality_domain,
    bv_pointerst &_solver, 
    const namespacet &_ns) : 
  strategy_solver_baset(program, _renaming_map, _solver, _ns),
  equality_domain(_equality_domain) 
  {
    //build work list for equalities
    for(var_listt::const_iterator v1 = equality_domain.get_vars().begin();
	v1 != equality_domain.get_vars().end(); v1++)
    {
      var_listt::const_iterator v2 = v1; v2++;
      for(;v2 != equality_domain.get_vars().end(); v2++)
      {
        todo_equs.insert(equality_domaint::var_pairt(*v1,*v2));
      }
    }
  }

  virtual bool iterate(invariantt &inv);

 protected:
  equality_domaint &equality_domain;

  typedef std::set<equality_domaint::var_pairt> worklistt;
  worklistt todo_equs;
  worklistt todo_disequs;
};

#endif
