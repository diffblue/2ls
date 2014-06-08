#ifndef CPROVER_INV_H
#define CPROVER_INV_H

#include <util/std_expr.h>

#include "template_domain.h"

typedef symbol_exprt loopvart;
typedef std::set<std::pair<loopvart,loopvart> > loopvarst;
typedef std::pair<symbol_exprt, bool> multiplexer_statet;

class invt
{
  
  invt(const class local_SSAt &program, loopvarst loopvars, 
    class strategy_solver_baset &_strategy_solver,
    class template_domaint &template_domain) :
    strategy_solver(_strategy_solver) {}

  void solve(class invariantt &inv);

 protected:
  class strategy_solver_baset &strategy_solver;

};

#endif
