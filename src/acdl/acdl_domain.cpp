/*******************************************************************\

Module: ACDL Solver

Author: Rajdeep Mukherjee, Peter Schrammel

\*******************************************************************/


#define DEBUG


#ifdef DEBUG
#include <iostream>
#endif

#include <util/simplify_expr.h>
#include <util/find_symbols.h>

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
  new_value = true_exprt();
  
#ifdef DEBUG
    std::cout << "[ACDL-DOMAIN] old value: "
	      << from_expr(SSA.ns, "", _old_value) << std::endl;
#endif

  ssa_analyzert ssa_analyzer;
  incremental_solvert *solver = incremental_solvert::allocate(SSA.ns,true);

  std::vector<valuet> new_values;
  new_values.reserve(vars.size());
  for(varst::const_iterator it = vars.begin();
      it != vars.end(); ++it)
  {
    // project _old_value on everything in statement but *it
    valuet old_value = remove_var(_old_value,*it);

#ifdef DEBUG
    std::cout << "[ACDL-DOMAIN] projected(" << it->get_identifier() << "): "
	      << from_expr(SSA.ns, "", old_value) << std::endl;
#endif

    template_generator_acdlt template_generator(options,ssa_db,ssa_local_unwinder); 
    template_generator(SSA,*it);
    
    ssa_analyzer(*solver, SSA, and_exprt(old_value,statement),template_generator);
    valuet var_value;
    ssa_analyzer.get_result(var_value,template_generator.all_vars());

    new_values.push_back(and_exprt(old_value,var_value));

#ifdef DEBUG
    std::cout << "[ACDL-DOMAIN] new_value(" << it->get_identifier() << "): "
	      << from_expr(SSA.ns, "", new_values.back()) << std::endl;
#endif
  }
    
  meet(new_values,new_value);

#ifdef DEBUG
    std::cout << "[ACDL-DOMAIN] new_value: "
	      << from_expr(SSA.ns, "", new_value) << std::endl;
#endif
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

bool acdl_domaint::contains(const valuet &value1, const valuet &value2) const
{
  incremental_solvert *solver = incremental_solvert::allocate(SSA.ns,true);
  *solver << and_exprt(value1,not_exprt(value2));
  bool result = (*solver)()==decision_proceduret::D_UNSATISFIABLE;
  delete solver;
  return result;
}

/*******************************************************************\

Function: acdl_domaint::is_bottom()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool acdl_domaint::is_bottom(const valuet &value) const
{
  incremental_solvert *solver = incremental_solvert::allocate(SSA.ns,true);
  *solver << value;
  bool result = (*solver)()==decision_proceduret::D_UNSATISFIABLE;
  delete solver;
  return result;
}

/*******************************************************************\

Function: acdl_domaint::is_complete()

  Inputs:

 Outputs:

 Purpose: This is a very stupid and restrictive gamma-completeness check

\*******************************************************************/

bool acdl_domaint::is_complete(const valuet &value) const
{
  incremental_solvert *solver = incremental_solvert::allocate(SSA.ns,true);
  *solver << value;
  
  decision_proceduret::resultt res = (*solver)();
  assert(res==decision_proceduret::D_SATISFIABLE);

  //TODO: 
  // find symbols on value
  // for each symbol x
  //   get model m from solver; exprt m = (*solver).get(x)
  exprt model = false_exprt();
    // and push !(x=m) into the solver
  *solver << model;
  
  bool result = (*solver)()==decision_proceduret::D_UNSATISFIABLE;
  delete solver;
  return result;
}

/*******************************************************************\

Function: acdl_domaint::remove_var()

  Inputs: example:
          Old_value = (1 <= x && x <= 5) && (0 <= y && y <= 10) vars = x

 Outputs: example:
          (0 <= y && y <= 10)

 Purpose:

\*******************************************************************/

exprt acdl_domaint::remove_var(const valuet &_old_value, const symbol_exprt &var)
{
  valuet old_value = _old_value;
  simplify(old_value,SSA.ns);
  
  valuet::operandst new_value;  
  for(valuet::operandst::const_iterator it = old_value.operands().begin();
        it != old_value.operands().end(); ++it)
  {
    find_symbols_sett symbols;
    find_symbols(*it,symbols);
    if(symbols.find(var.get_identifier()) == symbols.end())
      new_value.push_back(*it);
  }
  return conjunction(new_value);
}

/*******************************************************************\

Function: acdl_domaint::split()

  Inputs: example: 
            expr: x-y
            value: -1 <= x-y && x-y <= 5 && 0 <= y && y <= 10 && ...

 Outputs: example:
            2 <= x-y (for upper=true)

 Purpose:

\*******************************************************************/

exprt acdl_domaint::split(const valuet &value, const exprt &expr, 
			  bool upper)
{ 

    return value; 
}

