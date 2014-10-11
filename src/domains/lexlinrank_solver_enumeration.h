#ifndef CPROVER_LEXLINRANK_SOLVER_ENUMERATION_H 
#define CPROVER_LEXLINRANK_SOLVER_ENUMERATION_H 

#include "strategy_solver_base.h"
#include "lexlinrank_domain.h"
#include <solvers/sat/satcheck.h>
#include <solvers/flattening/bv_pointers.h>


class lexlinrank_solver_enumerationt : public strategy_solver_baset 
{
 public:
  explicit lexlinrank_solver_enumerationt(const constraintst &program,
					  lexlinrank_domaint &_lexlinrank_domain,
					  bv_pointerst &_solver, const namespacet &_ns) : 
  strategy_solver_baset(program, _solver, _ns),
    lexlinrank_domain(_lexlinrank_domain), 
    //inner_satcheck(),
    //inner_solver(_ns, inner_satcheck), 
    number_refinements(0)
  {
    inner_satcheck = new satcheck_minisat_no_simplifiert();
    inner_solver = new bv_pointerst(_ns, *inner_satcheck);
  }

  //inner_solver(_ns, inner_satcheck), 
  //number_outer_iterations(0),
  //number_refinements(0)
  //  {}

  virtual bool iterate(invariantt &inv);

 protected:
  lexlinrank_domaint &lexlinrank_domain;

  // the "inner" solver
  satcheck_minisat_no_simplifiert *inner_satcheck;

  bv_pointerst *inner_solver;
  unsigned number_refinements;

  bvt inner_formula;  

  //bv_pointerst inner_solver;
  //unsigned number_outer_iterations;
  //unsigned number_refinements;


};

#endif
