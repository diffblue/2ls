#ifndef CPROVER_STRATEGY_SOLVER_BINSEARCH3_H 
#define CPROVER_STRATEGY_SOLVER_BINSEARCH3_H 

#include "strategy_solver_base.h"
#include "tpolyhedra_domain.h"

class strategy_solver_binsearch3t : public strategy_solver_baset 
{
 public:
  explicit strategy_solver_binsearch3t(const constraintst &program,
    tpolyhedra_domaint &_tpolyhedra_domain,
    bv_pointerst &_solver, const namespacet &_ns) : 
    strategy_solver_baset(program, _solver, _ns),
    tpolyhedra_domain(_tpolyhedra_domain),
    sum_bound_counter(0) {}

  virtual bool iterate(invariantt &inv);

 protected:
  const constraintst &program;
  tpolyhedra_domaint &tpolyhedra_domain;
  unsigned sum_bound_counter;
  std::set<tpolyhedra_domaint::rowt> improve_rows;
  std::map<tpolyhedra_domaint::rowt,symbol_exprt> symb_values;
  std::map<tpolyhedra_domaint::rowt,constant_exprt> lower_values;

};

#endif
