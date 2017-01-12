/*******************************************************************\

Module: Transformer simplification

Author: Peter Schrammel

\*******************************************************************/

#include <cassert>

#include "simplify_transformer.h"
#include "simplify_transformer_class.h"
#include <util/std_expr.h>

#define DEBUGX

#ifdef DEBUGX
#include <langapi/language_util.h>
#include <iostream>
#endif

/*******************************************************************\

Function: simplify_transformert::collect_node

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void simplify_transformert::collect_node(const exprt &expr,
                                        replace_mapt &substitutions,
                                        bool frozen_only,
                                        bool make_copy)
{
  if(expr.id()==ID_equal)
  {
    const equal_exprt &e=to_equal_expr(expr);

    bool rhs_is_constant=e.rhs().id()==ID_constant;
    bool rhs_is_symbol=e.rhs().id()==ID_symbol ||
                       e.rhs().id()==ID_nondet_symbol;
    bool rhs_is_frozen=rhs_is_symbol &&
      frozen_symbols.find(e.rhs().get(ID_identifier))!=frozen_symbols.end();
    bool lhs_is_constant=e.lhs().id()==ID_constant;
    bool lhs_is_symbol=e.lhs().id()==ID_symbol ||
                       e.lhs().id()==ID_nondet_symbol;
    bool lhs_is_frozen=lhs_is_symbol &&
      frozen_symbols.find(e.lhs().get(ID_identifier))!=frozen_symbols.end();

    exprt lhs, rhs;
    lhs.make_nil();
    rhs.make_nil();
    // stupid matching
    if((rhs_is_frozen || rhs_is_constant || !frozen_only) &&
       lhs_is_symbol && !lhs_is_frozen)
    {
      lhs=e.lhs();
      rhs=e.rhs();
    }
    if((lhs_is_frozen || lhs_is_constant || !frozen_only) &&
       rhs_is_symbol && !rhs_is_frozen)
    {
      rhs=e.lhs();
      lhs=e.rhs();
    }
    if(rhs.is_not_nil() && lhs.is_not_nil())
    {
      if(make_copy) // make lazy copy
      {
        replace_mapt _subst=substitutions;
        substitutions=_subst;
      }
      substitutions[lhs]=rhs;
    }
  }

#ifdef DEBUGX
  std::cout << "COLLECT: " << from_expr(ns, "", expr) << std::endl;
  for(const auto &it : substitutions)
    std::cout << from_expr(ns, "", it.first)
            << "---> " << from_expr(ns, "", it.second)
            << "\n";
#endif
}

/*******************************************************************\

Function: simplify_transformert::simplify_node

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool simplify_transformert::simplify_node(exprt &expr,
                                         const replace_mapt &substitutions)
{
  return replace_expr(substitutions, expr);
}

/*******************************************************************\

Function: simplify_transformert::simplify_rec

  Inputs:

 Outputs: returns true if expression unchanged;
          returns false if changed

 Purpose:

\*******************************************************************/

bool simplify_transformert::simplify_rec(exprt &expr,
                                        replace_mapt &substitutions)
{
#ifdef DEBUGX
  exprt old(expr);
#endif

  bool result=true;
  if(expr.id()==ID_and)
  {
    // first propagate from frozen symbols
    bool res=false;
    do
    {
      Forall_operands(it, expr)
        collect_node(*it, substitutions, true, false);

      Forall_operands(it, expr)
        if(!simplify_rec(*it, substitutions))
          result=false;

      res=simplify_node(expr, substitutions);
      if(!res) result=false;
    }
    while(!res);

    // simplify remaining equalities
    Forall_operands(it, expr)
      collect_node(*it, substitutions, false, false);

    res=false;
    do
    {
      res=simplify_node(expr, substitutions);
      if(!res) result=false;
    }
    while(!res);
  }

#if 0 // for later extension to disjunctions
  // TODO: handle negation, too
  else if(expr.id()==ID_or || expr.id()==ID_implies)
  {
    Forall_operands(it, expr)
    {
      collect_node(*it, substitutions, true);
      if(!simplify_rec(*it, substitutions))
        result=false;

      bool res=false;
      do
      {
        res=simplify_node(*it, substitutions);
        if(!res) result=false;
      }
      while(!res);
    }
  }
#endif

#ifdef DEBUGX
  std::cout << "===== " << from_expr(ns, "", old)
            << "\n ---> " << from_expr(ns, "", expr)
            << "\n";
#endif

  return result;
}

/*******************************************************************\

Function: simplify_transformert::operator()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool simplify_transformert::operator()(exprt &expr)
{
  replace_mapt substitutions;
  return simplify_rec(expr, substitutions);
}

/*******************************************************************\

Function: simplify

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool simplify(exprt &expr,
              const std::set<irep_idt> &frozen_vars,
              const namespacet &ns)
{
  return simplify_transformert(ns, frozen_vars)(expr);
}

/*******************************************************************\

Function: simplify_transformer

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt simplify_transformer(const exprt &src,
                          const std::set<irep_idt> &frozen_vars,
                          const namespacet &ns)
{
#ifdef DEBUGX
  std::cout << "FROZEN:";
  for(const auto &it : frozen_vars)
    std::cout << " " << it;
  std::cout << "\n";
#endif

  exprt tmp=src;
  simplify_transformert(ns, frozen_vars)(tmp);
  return tmp;
}

