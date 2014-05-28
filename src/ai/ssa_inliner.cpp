#include <util/i2string.h>

#include "ssa_inliner.h"

void ssa_inlinert::replace(local_SSAt::nodet &node, 
                       local_SSAt::nodet::equalitiest::iterator equ_it, 
                       summaryt summary)
{
  function_application_exprt funapp_expr = to_function_application_expr(equ_it->rhs());
  local_SSAt::nodet::equalitiest new_equs;
  std::set<local_SSAt::nodet::equalitiest::iterator> rm_equs;

  counter++;

  //constraints for transformer
  exprt transformer = summary.transformer;
  rename(transformer);
  node.constraints.push_back(transformer);

  //constraints for return values
  exprt::operandst retvals;
  retvals.reserve(summary.exit_vars.size());
  for(summaryt::var_listt::const_iterator it3 = summary.exit_vars.begin();
      it3 != summary.exit_vars.end(); it3++)
  {
    symbol_exprt rhs = *it3;
    rename(rhs);
    retvals.push_back(equal_exprt(equ_it->lhs(),rhs));
  }
  node.constraints.push_back(disjunction(retvals));

  //equalities for arguments
  rm_equs.insert(equ_it);
  summaryt::var_listt::const_iterator it1 = summary.entry_vars.begin();
  for(exprt::operandst::const_iterator it2 = funapp_expr.arguments().begin();
      it2 != funapp_expr.arguments().end(); it2++, it1++)
  {
    assert(it1!=summary.entry_vars.end());
    exprt rhs = *it2;
    rename(rhs);
    new_equs.push_back(equal_exprt(*it1,rhs));
  }
  //remove obsolete equalities
  for(std::set<local_SSAt::nodet::equalitiest::iterator>::iterator it = rm_equs.begin();
      it != rm_equs.end(); it++) 
  {
    node.equalities.erase(*it);
  }
  //insert new equalities
  node.equalities.insert(node.equalities.end(),new_equs.begin(),new_equs.end());
}

void ssa_inlinert::replace(local_SSAt::nodet &node, 
                       local_SSAt::nodet::equalitiest::iterator equ_it, 
                       const local_SSAt &function)
{
  assert(false);
}

void ssa_inlinert::havoc(local_SSAt::nodet &node, 
	     local_SSAt::nodet::equalitiest::iterator &equ_it)
{
    node.equalities.erase(equ_it);
}

void ssa_inlinert::rename(exprt &expr) 
{
  if(expr.id()==ID_symbol) 
  {
    symbol_exprt &sexpr = to_symbol_expr(expr);
    irep_idt id = id2string(sexpr.get_identifier())+"@"+i2string(counter);
    sexpr.set_identifier(id);
  }
  for(exprt::operandst::iterator it = expr.operands().begin();
      it != expr.operands().end(); it++)
  {
    rename(*it);
  }
}
