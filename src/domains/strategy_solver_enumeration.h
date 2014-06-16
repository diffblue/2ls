#include "strategy_solver_base.h"

class strategy_solver_enumerationt : public strategy_solver_baset 
{
 public:
  explicit strategy_solver_enumerationt(const constraintst &program,
    replace_mapt &_renaming_map,
    template_domaint &_template_domain,
    bv_pointerst &_solver, const namespacet &_ns) : 
  strategy_solver_baset(program, _renaming_map, _template_domain, _solver, _ns) {}

  virtual void solve(invariantt &inv, const strategyt &strategy);

};
