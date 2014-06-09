#include "strategy_solver_base.h"

class strategy_solver_binsearcht : public strategy_solver_baset 
{
 public:
  strategy_solver_binsearcht(const local_SSAt &program, loopvarst loopvars, 
    template_domaint &template_domain) {}

  virtual void solve(invariantt &inv, const strategyt &strategy);

};
