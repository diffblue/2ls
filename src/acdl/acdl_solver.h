/*******************************************************************\

Module: ACDL Solver

Author: Rajdeep Mukherjee

\*******************************************************************/

#ifndef CPROVER_ACDL_SOLVER_H
#define CPROVER_ACDL_SOLVER_H

#include <util/options.h>
#include <goto-programs/property_checker.h>
#include "acdl_domain.h"

#include "../ssa/local_ssa.h"

class acdl_solvert : public messaget
{
public:

  //typedef std::list<exprt> worklist;
  //typedef exprt valuet;
  explicit acdl_solvert(const optionst &_options,
    acdl_domaint &_domain)
    : 
    options(_options),
    domain(_domain)
    {
    }  

  ~acdl_solvert() 
    {
    }

  property_checkert::resultt operator()(const local_SSAt &SSA);

protected:
  const optionst &options;
  acdl_domaint &domain;
  typedef std::set<acdl_domaint::statementt> worklistt;
  virtual void initialize_worklist(const local_SSAt &, worklistt &);
  virtual void select_vars(const exprt &statement, acdl_domaint::varst &vars);
  void update_worklist(const local_SSAt &SSA, const acdl_domaint::varst &vars, worklistt &worklist, const acdl_domaint::statementt &statement);
  bool check_statement (const exprt &expr, const acdl_domaint::varst &vars);

};


#endif
 
