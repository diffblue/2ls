/*******************************************************************\

Module: Second-Order Formula Builder

Author: Peter Schrammel

\*******************************************************************/

#define DEBUG

#ifdef DEBUG
#include <iostream>
#include <langapi/language_util.h>
#endif

#include "so_formula_builder.h"

/*******************************************************************\

Function: so_formula_buildert::predicate_identifier()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

irep_idt so_formula_buildert::predicate_identifier(
  std::string kind,
  irep_idt name,
  std::string instance)
{
  if(instance=="")
    return kind+"#"+id2string(name);
  else
    return kind+"#"+id2string(name)+"#"+instance;
}

/*******************************************************************\

Function: so_formula_buildert::summary()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

so_formulat so_formula_buildert::summary(const block_ssat &block)
{
  so_formulat so;
  //TODO
  return so;
} 

/*******************************************************************\

Function: so_formula_buildert::invariants()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

so_formulat so_formula_buildert::invariants(const block_ssat &block)
{
  so_formulat so;
  //TODO
  return so;
} 

/*******************************************************************\

Function: so_formula_buildert::calling_contexts()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

so_formulat so_formula_buildert::calling_contexts(const block_ssat &block)
{
  so_formulat so;
  //TODO
  return so;
} 

/*******************************************************************\

Function: so_formula_buildert::recsum()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

so_formulat so_formula_buildert::recsum(const block_ssat &block)
{
  predicate_symbol_exprt pre0=make_pre("PRE0",block);
  predicate_symbol_exprt pre=make_pre("PRE",block);
  predicate_symbol_exprt post=make_post("POST",block);
  predicate_symbol_exprt sum=make_sum("SUM",block);
  predicate_symbol_sett preds;
  preds.insert(pre);
  preds.insert(post);
  preds.insert(sum);
  implies_exprt base(apply(pre0,block.inputs),
                     apply(pre,block.inputs));
  exprt::operandst lhs, rhs;
  lhs.push_back(equal_exprt(block.guard_in,
                            apply(pre,block.inputs)));
  for(const auto &bc: block.block_calls)
  {
    if(bc.identifier==block.identifier) //recursive call
    {
      lhs.push_back(equal_exprt(bc.cond_term,
                                apply(post,bc.returns)));
      rhs.push_back(implies_exprt(bc.guard_call,
                                  apply(pre,bc.arguments)));
    }
    else
    {
      predicate_symbol_exprt sumc=make_sum("SUM0",bc);
      exprt::operandst sumvars;
      add_vars(sumvars, bc.arguments);
      add_vars(sumvars, bc.returns);
      lhs.push_back(implies_exprt(and_exprt(bc.guard_call,bc.cond_term),
                                  apply(sumc,sumvars)));
    }
  }
  lhs.push_back(make_block(block));
  rhs.push_back(implies_exprt(block.guard_out,
                              apply(post,block.outputs)));
  exprt::operandst sum_vars;
  add_vars(sum_vars,block.inputs);
  add_vars(sum_vars,block.outputs);
  rhs.push_back(implies_exprt(and_exprt(block.guard_in,block.guard_out),
                                apply(sum,sum_vars)));
  implies_exprt step(conjunction(lhs),conjunction(rhs));
  and_exprt cases(base,step);
  exprt sof=add_preamble(preds, cases);
  return so_formulat(sof);
} 

/*******************************************************************\

Function: so_formula_buildert::make_block()

  Inputs:

 Outputs:

 Purpose: creates a place holder for the block's code

\*******************************************************************/

function_application_exprt so_formula_buildert::make_block(const block_ssat &block)
{
  function_application_exprt expr;
  expr.function()=symbol_exprt(block.identifier);
  //TODO: add type for consistency checking
  return expr;
}

/*******************************************************************\

Function: so_formula_buildert::make_preamble()

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

exprt so_formula_buildert::add_preamble(
  predicate_symbol_sett &symbols, const exprt &expr)
{
  if(symbols.empty())
  {
    forall_exprt forall;
    //TODO: currently we assume all variables are universally quantified
    forall.where()=expr;
    return forall;
  }

  predicate_symbol_sett::iterator p_it=symbols.begin();
  exists_exprt e;
  e.symbol()=*p_it;
  symbols.erase(p_it);
  e.where()=add_preamble(symbols, expr);
  return e;
} 

/*******************************************************************\

Function: so_formula_buildert::make_pre()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

predicate_symbol_exprt so_formula_buildert::make_pre(std::string prefix, const block_ssat &block)
{
  predicate_typet t;
  //TODO
  predicate_symbol_exprt p(predicate_identifier(prefix,block.identifier), t);
  return p;
} 

/*******************************************************************\

Function: so_formula_buildert::post()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

predicate_symbol_exprt so_formula_buildert::make_post(std::string prefix, const block_ssat &block)
{
  predicate_typet t;
  //TODO
  predicate_symbol_exprt p(predicate_identifier(prefix,block.identifier), t);
  return p;
} 

/*******************************************************************\

Function: so_formula_buildert::sum()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

predicate_symbol_exprt so_formula_buildert::make_sum(std::string prefix, const block_ssat &block)
{
  predicate_typet t;
  //TODO
  predicate_symbol_exprt p(predicate_identifier(prefix,block.identifier), t);
  return p;
} 

predicate_symbol_exprt so_formula_buildert::make_sum(std::string prefix, const block_ssat::block_call_infot &block_call)
{
  predicate_typet t;
  //TODO
  predicate_symbol_exprt p(predicate_identifier(prefix,block_call.identifier), t);
  return p;
}

/*******************************************************************\

Function: so_formula_buildert::apply()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

predicate_application_exprt so_formula_buildert::apply(
    const predicate_symbol_exprt &symbol,
    const exprt::operandst &arguments)
{
  //TODO: check consistency of args
  predicate_application_exprt e(symbol);
  e.arguments()=arguments;
  return e;
}

/*******************************************************************\

Function: so_formula_buildert::apply()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

predicate_application_exprt so_formula_buildert::apply(
    const predicate_symbol_exprt &symbol,
    const block_ssat::varst &arguments)
{
  exprt::operandst args;
  add_vars(args, arguments);
  return apply(symbol, args);
}

/*******************************************************************\

Function: so_formula_buildert::add_vars()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void so_formula_buildert::add_vars(
  exprt::operandst &v, const block_ssat::varst &vars)
{
  for(const auto &i : vars)
    v.push_back(i);
}
