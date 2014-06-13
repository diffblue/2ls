#include "strategy_solver_base.h"

class strategy_solver_enumerationt : public strategy_solver_baset 
{
 public:
  explicit strategy_solver_enumerationt(const constraintst &program,
    var_listt &_pre_state_vars, var_listt &_post_state_vars,
    template_domaint &_template_domain,
    bv_pointerst &_solver, const namespacet &_ns) : 
  strategy_solver_baset(program, _pre_state_vars, _post_state_vars, _template_domain, _solver, _ns) {}

  virtual void solve(invariantt &inv, const strategyt &strategy);

};
