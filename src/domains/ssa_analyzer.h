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

protected:
  const namespacet &ns;
  optionst &options;
  strategy_solver_baset::invariantt inv;
  unsigned iteration_number;
};


#endif
