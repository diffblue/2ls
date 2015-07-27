
#include <util/simplify_expr.h>

#include "acdl_domain.h"

/*******************************************************************\

Function: acdl_domaint::operator()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/


void acdl_domaint::operator()(const statementt &statement,
		  const varst &vars,
		  const valuet &_old_value,
		  valuet &new_value)
{
#if 0
  ssa_analyzert ssa_analyzer;
  incremental_solvert *solver = incremental_solvert::allocate(ns,true);
  local_SSAt SSA; //TODO [Peter]: get a dummy SSA from somewhere
  SSA.mark_nodes();

  std::vector<valuet> new_values;
  new_values.reserve(vars.size());
  for(varst::const_iterator it = vars.begin();
      it != vars.end(); ++it)
  {
    exprt old_value = _old_value;
    //TODO [Rajdeep]: project _old_value on everything in statement but *it
    remove_var(old_value,*it);
    
    template_generator_acdlt template_generator; //TODO [Peter]
    template_generator(*it);
    
    ssa_analyzer(*solver, SSA, and_exprt(old_value,statement),template_generator);
    ssa_analyzer.get_result(var_value);

    new_values.push_back(and_exprt(old_value,var_value));
  }
  meet(new_values,new_value);
  delete solver;
#endif
}

/*******************************************************************\

Function: acdl_domaint::meet()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void acdl_domaint::meet(const std::vector<valuet> &old_values,
	    valuet &new_value)
{
  new_value = conjunction(old_values);
  simplify(new_value,ns);
}


/*******************************************************************\

Function: acdl_domaint::join()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void acdl_domaint::join(const std::vector<valuet> &old_values,
	    valuet &new_value)
{
  new_value = disjunction(old_values);
  simplify(new_value,ns);
}

  
/*******************************************************************\

Function: acdl_domaint::contains()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool acdl_domaint::contains(const valuet &new_value,
		const valuet &old_value)
{
  incremental_solvert *solver = incremental_solvert::allocate(ns,true);
  *solver << and_exprt(new_value,not_exprt(old_value));
  bool result = (*solver)()==decision_proceduret::D_UNSATISFIABLE;
  delete solver;
  return result;
}
