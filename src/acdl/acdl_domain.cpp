/*******************************************************************\

Module: ACDL Domain

Author: Rajdeep Mukherjee, Peter Schrammel

\*******************************************************************/


#define DEBUG


#ifdef DEBUG
#include <iostream>
#endif

#include <util/simplify_expr.h>
#include <util/find_symbols.h>
#include <memory>

#include "../domains/ssa_analyzer.h"
#include "../domains/tpolyhedra_domain.h"

#include "acdl_domain.h"
#include "template_generator_acdl.h"

/*******************************************************************\

Function: acdl_domaint::operator()

  Inputs:

 Outputs:

 Purpose: operator()

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
  std::unique_ptr<incremental_solvert> solver(incremental_solvert::allocate(SSA.ns,true));

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

    // booleans
    if(it->type().id()==ID_bool)
    {
      valuet var_value;
      literalt l = solver->solver->convert(*it);
      if(l.is_true()) 
	      var_value = *it;
      else if(l.is_false())
	      var_value = not_exprt(*it);
      else
      {
	      solver->solver->set_frozen(l);
	      *solver << and_exprt(old_value,statement);
	
        if((*solver)() == decision_proceduret::D_SATISFIABLE)
        {
          exprt m = (*solver).get(*it);
          if(m.is_true())
            var_value = *it;
          else
            var_value = not_exprt(*it);
          solver->new_context();
          *solver << not_exprt(*it);
          if((*solver)() == decision_proceduret::D_SATISFIABLE)
            var_value = true_exprt(); //don't know
          solver->pop_context();
        }
        else //bottom
          var_value = false_exprt();
      }

      new_values.push_back(and_exprt(old_value,var_value));
    }
    // numerical variables using templates
    else if (it->type().id() == ID_signedbv ||
        it->type().id() == ID_unsignedbv ||
        it->type().id() == ID_floatbv)
    {
      template_generator_acdlt template_generator(
          options,ssa_db,ssa_local_unwinder); 
      template_generator(SSA,*it);

      ssa_analyzer(*solver, SSA, and_exprt(old_value,statement),
          template_generator);
      valuet var_value;
      ssa_analyzer.get_result(var_value,template_generator.all_vars());

      new_values.push_back(and_exprt(old_value,var_value));
    }
    else
    {
      warning() << "WARNING: do not know how to propagate " 
        << it->get_identifier()
        << " of type " << from_type(SSA.ns, "", it->type()) 
        << eom;
    }


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

Function: acdl_domaint::meet()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void acdl_domaint::meet(const valuet &old_value,
	    valuet &new_value)
{
  new_value = and_exprt(old_value, new_value);
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
  std::unique_ptr<incremental_solvert> solver(incremental_solvert::allocate(SSA.ns,true));
  *solver << and_exprt(value1,not_exprt(value2));
  bool result = (*solver)()==decision_proceduret::D_UNSATISFIABLE;
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
  std::unique_ptr<incremental_solvert> solver(incremental_solvert::allocate(SSA.ns,true));
  *solver << value;
  bool result = (*solver)()==decision_proceduret::D_UNSATISFIABLE;
  return result;
}

/*******************************************************************\

Function: acdl_domaint::is_complete()

  Inputs:

 Outputs:

 Purpose: This is a very stupid and restrictive gamma-completeness check

\*******************************************************************/

bool acdl_domaint::is_complete(const valuet &value, const varst& symbols) const
{
#ifdef DEBUG
  std::cout << "[ACDL-DOMAIN] is_complete? "
	    << from_expr(SSA.ns, "", value);
//	    << std::endl;
#endif

    
  std::unique_ptr<incremental_solvert> solver(incremental_solvert::allocate(SSA.ns,true));
  *solver << value;
    
#if 0
  // find symbols in value
  std::set<symbol_exprt> symbols;
  find_symbols (value, symbols);
#endif

  for(std::set<symbol_exprt>::const_iterator it = symbols.begin();
      it != symbols.end(); ++it)
  {
    decision_proceduret::resultt res = (*solver)();
    assert(res==decision_proceduret::D_SATISFIABLE);
    // if value == (x=[2,2]) and (*it is x), then 'm' below contains the
    // value of x which is 2
    exprt m = (*solver).get(*it);
    solver->new_context();

#if 0
    std::cout << "  check "
	      << from_expr(SSA.ns, "", not_exprt(equal_exprt(*it,m)))
	      << std::endl;
#endif
  
    // and push !(x=m) into the solver
    *solver << not_exprt(equal_exprt(*it,m));
  
    if((*solver)()!=decision_proceduret::D_UNSATISFIABLE)
    {
#ifdef DEBUG
      std::cout << " is not complete" << std::endl;
#endif
      return false;
    }

    solver->pop_context();
  }
  
#ifdef DEBUG
  std::cout << " is complete" << std::endl;
#endif
  return true;
}

/*******************************************************************\

Function: acdl_domaint::remove_var()

  Inputs: example:
          Old_value = (1 <= x && x <= 5) && (0 <= y && y <= 10) vars = x

 Outputs: example:
          (0 <= y && y <= 10)

 Purpose:

\*******************************************************************/

exprt acdl_domaint::remove_var(const valuet &_old_value, 
			       const symbol_exprt &var)
{
  valuet old_value = _old_value;
  simplify(old_value,SSA.ns);

  if(old_value.id() == ID_and)
  {
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

  find_symbols_sett symbols;
  find_symbols(old_value,symbols);
  if(symbols.find(var.get_identifier()) != symbols.end())
    return true_exprt();

  return old_value;
}

/*******************************************************************\

Function: acdl_domaint::split()

  Inputs: example: 
            expr: x-y
            value: -(x-y) <= 1 && x-y <= 5 && -y <= 0 && y <= 10 && ...
          This is very generic, can be easily extended to octagons and 
          other richer domains
 Outputs: example:
            2 <= x-y (for upper=true)

 Purpose: splits constant-bounded expressions in half
          If the expression is already a singleton then we cannot split
          and we return false. 

\*******************************************************************/

exprt acdl_domaint::split(const valuet &value, const exprt &expr, 
			  bool upper)
{ 
  std::cout << "[ACDL-DOMAINS] Inside split decision: "
	      << value.pretty() << std::endl;
        
  if(expr.type().id()==ID_bool)
  {
    exprt v_true = simplify_expr(and_exprt(value,expr),SSA.ns);
    if(v_true.is_false())
      return false_exprt();
    exprt v_false = simplify_expr(and_exprt(value,not_exprt(expr)),SSA.ns);
    if(v_false.is_true())
      return false_exprt();
    if(upper) {
      std::cout << "[ACDL-DOMAINS] Inside split decision Upper: "
	      << value.pretty() << std::endl;
      return expr;
    }
    else
      return not_exprt(expr);
  }

  if(!(expr.type().id() == ID_signedbv ||
     expr.type().id() == ID_unsignedbv ||
       expr.type().id() == ID_floatbv))
  {
    warning() << "WARNING: do not know how to split " 
	      << from_expr(SSA.ns, "", expr)
	      << " of type " << from_type(SSA.ns, "", expr.type()) 
	      << eom;
    return false_exprt(); 
  }

  if(value.operands().size()<2)
    return true_exprt(); //cannot split

  assert(value.id()==ID_and); //is a conjunction
  
  //match template expression
  constant_exprt u;
  for(unsigned i=0; i<value.operands().size(); i++)
  {
    const exprt &e = value.operands()[i];
    if(e.id() != ID_le)
      continue;
    if(to_binary_relation_expr(e).lhs() == expr)
    {
      u = to_constant_expr(to_binary_relation_expr(e).rhs());
      break;
    }
  }
  constant_exprt l;
  for(unsigned i=0; i<value.operands().size(); i++)
  {
    const exprt &e = value.operands()[i];
    if(e.id() != ID_le)
      continue;
    const exprt &lhs = to_binary_relation_expr(e).lhs();
    if(lhs.id()==ID_unary_minus && 
       lhs.op0().id()==ID_typecast &&
       lhs.op0().op0() == expr)
    {
      l = to_constant_expr(to_binary_relation_expr(e).rhs());
      break;
    }
  }

  //TODO: check whether we have a singleton, then we cannot split anymore
  exprt m = tpolyhedra_domaint::between(l,u);

  std::cout << "[ACDL-DOMAINS] decision: "
	      << from_expr(SSA.ns, "", binary_relation_exprt(m,ID_le,expr)) << std::endl;
  if(upper) {
#ifdef DEBUG
    std::cout << "[ACDL-DOMAIN] decision: "
	      << from_expr(SSA.ns, "", binary_relation_exprt(m,ID_le,expr)) << std::endl;
#endif
    return binary_relation_exprt(m,ID_le,expr);
  }
  else {
#ifdef DEBUG
    std::cout << "[ACDL-DOMAIN] decision: "
	      << from_expr(SSA.ns, "", binary_relation_exprt(expr,ID_le,m)) << std::endl;
#endif
    return binary_relation_exprt(expr,ID_le,m);
  }
}

/*******************************************************************\

Function: acdl_domaint::normalize()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void acdl_domaint::normalize(valuet &value, const varst &vars)
{
  valuet old_value = value;

  std::vector<symbol_exprt> clean_vars;
  
  //project out vars
  for(varst::const_iterator it = vars.begin();
      it != vars.end(); ++it)
  {
    // we only normalize what the abstract domain currently handles
    if(it->type().id() == ID_signedbv ||
       it->type().id() == ID_unsignedbv ||
       it->type().id() == ID_floatbv)
    {
      value = remove_var(value,*it);
      clean_vars.push_back(*it);
    }
  }
    
  ssa_analyzert ssa_analyzer;
  std::unique_ptr<incremental_solvert> solver(incremental_solvert::allocate(SSA.ns,true));

  template_generator_acdlt template_generator(options,ssa_db,ssa_local_unwinder); 
  template_generator(SSA,clean_vars);
    
  ssa_analyzer(*solver, SSA, old_value,template_generator);
  valuet new_values;
  ssa_analyzer.get_result(new_values,template_generator.all_vars());

    
  value = and_exprt(new_values,value);
}
