/*******************************************************************\

Module: Data Flow Analysis

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef DELTACHECK_SSA_ANALYZER_H
#define DELTACHECK_SSA_ANALYZER_H

#include <util/replace_expr.h>

#include "../ssa/local_ssa.h"
#include "strategy_solver_base.h"
#include "template_generator_base.h"

#define BINSEARCH_SOLVER strategy_solver_binsearcht

class ssa_analyzert : public messaget
{
public:
  typedef strategy_solver_baset::constraintst constraintst;
  typedef strategy_solver_baset::var_listt var_listt;

  explicit ssa_analyzert()
    : 
    solver_calls(0)
    {
    }  

    ~ssa_analyzert() 
    {
      if(result!=NULL) delete result;
    }

  void operator()(incremental_solvert &solver,
		  local_SSAt &SSA, 
                  const exprt &precondition,
                  template_generator_baset &template_generator);

  void get_result(exprt &result, const domaint::var_sett &vars);

  unsigned get_number_of_solver_calls() { return solver_calls; }

protected:
  domaint *domain; //template generator is responsable for the domain object
  domaint::valuet *result;

  //statistics
  unsigned solver_calls;
};


#endif
