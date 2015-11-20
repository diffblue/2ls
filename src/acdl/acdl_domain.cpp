
#include <util/simplify_expr.h>

#include "../domains/ssa_analyzer.h"

#include "acdl_domain.h"
#include "template_generator_acdl.h"

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
  ssa_analyzert ssa_analyzer;
  incremental_solvert *solver = incremental_solvert::allocate(SSA.ns,true);

  std::vector<valuet> new_values;
  new_values.reserve(vars.size());
  for(varst::const_iterator it = vars.begin();
      it != vars.end(); ++it)
  {
    valuet old_value = _old_value;
    //TODO [Rajdeep]: project _old_value on everything in statement but *it
#if 0
    remove_var(old_value,*it);
#endif
    
    template_generator_acdlt template_generator(options,ssa_db,ssa_local_unwinder); 
    template_generator(SSA,*it);
    
    ssa_analyzer(*solver, SSA, and_exprt(old_value,statement),template_generator);
    valuet var_value;
    ssa_analyzer.get_result(var_value,template_generator.all_vars());

    new_values.push_back(and_exprt(old_value,var_value));
  }
  meet(new_values,new_value);
  delete solver;
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
  new_value = and_exprt(conjunction(old_values), new_value);
  simplify(new_value,SSA.ns);
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
  new_value = or_exprt(disjunction(old_values), new_value);
  simplify(new_value,SSA.ns);
}

  
/*******************************************************************\

Function: acdl_domaint::contains()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool acdl_domaint::contains(const valuet &value1,
		const valuet &value2)
{
  incremental_solvert *solver = incremental_solvert::allocate(SSA.ns,true);
  *solver << and_exprt(value1,not_exprt(value2));
  bool result = (*solver)()==decision_proceduret::D_UNSATISFIABLE;
  delete solver;
  return result;
}


/*******************************************************************\

Function: acdl_domaint::remove_var()

  Inputs: Old_value = (1 <= x && x <= 5) && (0 <= y && y <= 10) vars = x

 Outputs: (0 <= y && y <= 10)

 Purpose:

\*******************************************************************/

exprt acdl_domaint::remove_var(const valuet &_old_value, const varst &vars)
{
  valuet::operandst expr_val;  
  irep_idt sym_name;
  // check only if the front element of the vector needs to be projected or 
  // we need to iterate over the vector
  irep_idt var_name = vars.front().get_identifier(); 
  for(valuet::operandst::const_iterator
        it = _old_value.operands().begin();
        it != _old_value.operands().end();
        ++it)
  {
    exprt sym_expr = *it;
    forall_operands(it1, sym_expr) {
      symbol_exprt curr_symbol = to_symbol_expr(*it1);
      sym_name = curr_symbol.get_identifier(); 
      if(sym_name == var_name)
       expr_val.push_back(*it);   
    }
  }
  exprt conjunction_exprt = conjunction(expr_val);
  return conjunction_exprt;
}
