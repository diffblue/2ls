/*******************************************************************\

Module: Bounds simplification

Author: Peter Schrammel

\*******************************************************************/

#include <cassert>

#include "simplify_bounds.h"
#include "simplify_bounds_class.h"
#include <util/std_expr.h>

#define DEBUGX

#ifdef DEBUGX
#include <langapi/language_util.h>
#include <iostream>
#endif

/*******************************************************************\

Function: simplify_boundst::get_min_bound

  Inputs:

 Outputs: 

 Purpose:

\*******************************************************************/

bool simplify_boundst::get_min_bound(const exprt &expr, mp_integer &value)
{
#ifdef DEBUGX
  std::cout << "get_min_bound: " << from_expr(ns, "", expr)
            << "\n";
#endif

  if(!is_bitvector_type(expr.type()))
    return false;

  if(expr.id()==ID_symbol)
  {
    value=get_smallest(expr.type());
    return true;
  }
  else if(expr.id()==ID_typecast)
  {
    return get_min_bound(to_typecast_expr(expr).op(), value);
  }
  else if(expr.id()==ID_unary_minus)
  {
    bool result=get_max_bound(to_unary_minus_expr(expr).op(), value);
    value=-value;
    return result;
  }
  else if(expr.id()==ID_plus)
  {
    mp_integer vr, vl;
    bool rr=get_min_bound(expr.op0(), vr);
    bool rl=get_min_bound(expr.op1(), vl);
    if(rr && rl)
    {
      value=vr+vl;
      return true;
    }
  }
  else if(expr.id()==ID_minus)
  {
    mp_integer vr, vl;
    bool rr=get_min_bound(expr.op0(), vr);
    bool rl=get_max_bound(expr.op1(), vl);
    if(rr && rl)
    {
      value=vr-vl;
      return true;
    }
  }

  return false;
}

/*******************************************************************\

Function: simplify_boundst::get_max_bound

  Inputs:

 Outputs: 

 Purpose:

\*******************************************************************/

bool simplify_boundst::get_max_bound(const exprt &expr, mp_integer &value)
{
#ifdef DEBUGX
  std::cout << "get_max_bound: " << from_expr(ns, "", expr)
            << "\n";
#endif

  if(!is_bitvector_type(expr.type()))
    return false;

  if(expr.id()==ID_symbol)
  {
    value=get_largest(expr.type());
    return true;
  }
  else if(expr.id()==ID_typecast)
  {
    return get_max_bound(to_typecast_expr(expr).op(), value);
  }
  else if(expr.id()==ID_unary_minus)
  {
    bool result=get_min_bound(to_unary_minus_expr(expr).op(), value);
    value=-value;
    return result;
  }
  else if(expr.id()==ID_plus)
  {
    mp_integer vr, vl;
    bool rr=get_max_bound(expr.op0(), vr);
    bool rl=get_max_bound(expr.op1(), vl);
    if(rr && rl)
    {
      value=vr+vl;
      return true;
    }
  }
  else if(expr.id()==ID_minus)
  {
    mp_integer vr, vl;
    bool rr=get_max_bound(expr.op0(), vr);
    bool rl=get_min_bound(expr.op1(), vl);
    if(rr && rl)
    {
      value=vr-vl;
      return true;
    }
  }

  return false;
}

/*******************************************************************\

Function: simplify_boundst::simplify_rec

  Inputs:

 Outputs: returns true if expression unchanged;
          returns false if changed

 Purpose:

\*******************************************************************/

bool simplify_boundst::simplify_rec(exprt &expr)
{
#ifdef DEBUGX
  exprt old(expr);
#endif

  bool result=true;
  if(expr.id()==ID_le)
  {
    binary_relation_exprt &e = to_binary_relation_expr(expr);
    if(is_bitvector_type(e.rhs().type()) && e.rhs().id()==ID_constant &&
       e.lhs().id()!=ID_symbol)
    {
      mp_integer rhs_value, lhs_max, lhs_min;
      to_integer(e.rhs(), rhs_value);
      if(get_max_bound(e.lhs(), lhs_max))
      {
        if(lhs_max<=rhs_value)
        {
          expr=true_exprt();
          result=false;
        }
        else
          result=clean_up_typecast(expr,rhs_value);
      }
      else if(get_min_bound(e.lhs(), lhs_min))
      {
        if(lhs_min>rhs_value)
        {
          expr=false_exprt();
          result=false;
        }
      }
    }
  }
  else if(expr.id()==ID_ge)
  {
    binary_relation_exprt &e = to_binary_relation_expr(expr);
    if(is_bitvector_type(e.rhs().type()) && e.rhs().id()==ID_constant &&
       e.lhs().id()!=ID_symbol)
    {
      mp_integer rhs_value, lhs_max, lhs_min;
      to_integer(e.rhs(), rhs_value);
      if(get_max_bound(e.lhs(), lhs_max))
      {
        if(lhs_max<rhs_value)
        {
          expr=false_exprt();
          result=false;
        }
      }
      else if(get_min_bound(e.lhs(), lhs_min))
      {
        if(lhs_min>=rhs_value)
        {
          expr=true_exprt();
          result=false;
        }
      }
    }
  }
  else if(expr.id()==ID_lt)
  {
    binary_relation_exprt &e = to_binary_relation_expr(expr);
    if(is_bitvector_type(e.rhs().type()) && e.rhs().id()==ID_constant &&
       e.lhs().id()!=ID_symbol)
    {
      mp_integer rhs_value, lhs_max, lhs_min;
      to_integer(e.rhs(), rhs_value);
      if(get_max_bound(e.lhs(), lhs_max))
      {
        if(lhs_max<rhs_value)
        {
          expr=true_exprt();
          result=false;
        }
      }
      else if(get_min_bound(e.lhs(), lhs_min))
      {
        if(lhs_min>=rhs_value)
        {
          expr=false_exprt();
          result=false;
        }
      }
    }
  }
  else if(expr.id()==ID_gt)
  {
    binary_relation_exprt &e = to_binary_relation_expr(expr);
    if(is_bitvector_type(e.rhs().type()) && e.rhs().id()==ID_constant &&
       e.lhs().id()!=ID_symbol)
    {
      mp_integer rhs_value, lhs_max, lhs_min;
      to_integer(e.rhs(), rhs_value);
      if(get_max_bound(e.lhs(), lhs_max))
      {
        if(lhs_max<=rhs_value)
        {
          expr=false_exprt();
          result=false;
        }
      }
      else if(get_min_bound(e.lhs(), lhs_min))
      {
        if(lhs_min>rhs_value)
        {
          expr=true_exprt();
          result=false;
        }
      }
    }
  }
  else 
  {
    Forall_operands(it, expr)
      if(!simplify_rec(*it))
        result=false;
  }
#ifdef DEBUGX
  std::cout << "===== " << from_expr(ns, "", old)
            << "\n ---> " << from_expr(ns, "", expr)
            << "\n";
#endif
    
  return result;
}

/*******************************************************************\

Function: simplify_boundst::clean_up_typecast

  Inputs:

 Outputs: 

 Purpose:

\*******************************************************************/

bool simplify_boundst::clean_up_typecast(exprt &expr, 
                                         const mp_integer &rhs_value)
{
  if(expr.id()==ID_le && expr.op0().id()==ID_unary_minus &&
     expr.op0().op0().id()==ID_typecast)
  {
    const typet &inner_type=expr.op0().op0().op0().type();
    if(-rhs_value>get_smallest(inner_type))
    {
      expr=binary_relation_exprt(expr.op0().op0().op0(), ID_ge,
                                 from_integer(-rhs_value,inner_type));
      return true;
    }
  }
  return false;
}

/*******************************************************************\

Function: simplify_boundst::clean_up_implications

  Inputs:

 Outputs: 

 Purpose:

\*******************************************************************/

bool simplify_boundst::clean_up_implications(exprt &expr)
{
  bool result=true;
  if(expr.id()==ID_and)
  {
    Forall_operands(it, expr)
      if(!clean_up_implications(*it))
        result=false;
    exprt::operandst::iterator it=expr.operands().begin();
    while(it!=expr.operands().end())
    {
      if(it->is_true())
        it=expr.operands().erase(it);
      else 
        ++it;
    }
    if(expr.operands().empty())
      expr=true_exprt();
    else if(expr.operands().size()==1)
      expr=expr.op0();
  }  
  else if(expr.id()==ID_implies)
  {
    if(expr.op1().is_true())
    {
      expr=true_exprt();
      result=false;
    }
  }
  return result;
}

/*******************************************************************\

Function: simplify_boundst::clean_up_implications

  Inputs:

 Outputs: 

 Purpose:

\*******************************************************************/

bool simplify_boundst::regroup_implications(exprt &expr)
{
  std::map<exprt, exprt::operandst> implication_map;
  exprt::operandst r;
  if(expr.id()==ID_and)
  {
    Forall_operands(it, expr)
      if(it->id()==ID_implies)
        implication_map[it->op0()].push_back(it->op1());
      else 
        r.push_back(*it);
  }
  else
    return true;
  for(auto &i : implication_map)
    r.push_back(implies_exprt(i.first, conjunction(i.second)));
  expr=conjunction(r);
  return false;
}

/*******************************************************************\

Function: simplify_boundst::operator()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool simplify_boundst::operator()(exprt &expr)
{
  bool result=simplify_rec(expr);
  if(!clean_up_implications(expr))
    result=false;
  if(!regroup_implications(expr))
    result=false;
  return result;
}

/*******************************************************************\

Function: simplify

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool simplify_bounds(exprt &expr, 
              const namespacet &ns)
{
  return simplify_boundst(ns)(expr);
}

/*******************************************************************\

Function: simplify_bounds

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt simplify_bounds(const exprt &src, 
                      const namespacet &ns)
{
  exprt tmp=src;
  simplify_boundst simplify_bounds(ns);
  simplify_bounds(tmp);
  return tmp;
}

