/*******************************************************************\

Module: Data Flow Analysis

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef DELTACHECK_SSA_ANALYZER_H
#define DELTACHECK_SSA_ANALYZER_H

#include <util/replace_expr.h>

#include "../ssa/local_ssa.h"
#include "strategy_solver_base.h"
#include "linrank_domain.h"
#include "lexlinrank_domain.h"
#include "template_generator_base.h"

#define LEXICOGRAPHIC

class ssa_analyzert : public messaget
{
public:
  typedef strategy_solver_baset::constraintst constraintst;
  typedef strategy_solver_baset::var_listt var_listt;

  explicit ssa_analyzert(const namespacet &_ns, 
                         const optionst &_options)
    : 
    compute_ranking_functions(false),
    ns(_ns),
    options(_options),
    solver_calls(0)
    {
    }  

    ~ssa_analyzert() 
    {
      if(domain!=NULL) delete domain;
      if(result!=NULL) delete result;
    }

  void operator()(local_SSAt &SSA, 
                  const exprt &precondition,
                  template_generator_baset &template_generator);

  void get_result(exprt &result, const domaint::var_sett &vars);

  bool compute_ranking_functions;

  unsigned get_number_of_solver_calls() { return solver_calls; }

protected:
  const namespacet &ns;
  const optionst &options;

  domaint *domain;
  domaint::valuet *result;

  //statistics
  unsigned solver_calls;
};


#endif
