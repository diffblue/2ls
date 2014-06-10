/*******************************************************************\

Module: Data Flow Analysis

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef DELTACHECK_SSA_ANALYZER_H
#define DELTACHECK_SSA_ANALYZER_H

#include "../ssa/local_ssa.h"
#include "strategy_solver_base.h"

class ssa_analyzert
{
public:
  typedef strategy_solver_baset::constraintst constraintst;
  typedef strategy_solver_baset::var_listt var_listt;

  explicit ssa_analyzert(const namespacet &_ns, 
                         optionst &_options)
    : ns(_ns),
      options(_options)
  {
  }  

  void operator()(local_SSAt &SSA);

  exprt get_result();
  exprt get_result(var_listt vars); //projects on vars

protected:
  const namespacet &ns;
  optionst &options;
  strategy_solver_baset::invariantt inv;
  unsigned iteration_number;

  void add_vars(const var_listt &vars_to_add, var_listt &vars);
  void add_vars(const local_SSAt::var_listt &vars_to_add, var_listt &vars);
  void add_vars(const local_SSAt::var_sett &vars_to_add, var_listt &vars);

};


#endif
