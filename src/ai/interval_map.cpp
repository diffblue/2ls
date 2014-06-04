/*******************************************************************\

Module: Interval maps

Author: Bjorn Wachter

\*******************************************************************/

#include <map>
#include <iostream>

#include <util/std_expr.h>
#include <util/arith_tools.h>
#include <langapi/language_util.h>

#include "interval_map.h"


bool interval_mapt::join(const interval_mapt &b)
{
  bool result=false;

  for(int_mapt::iterator it=int_map.begin();
      it!=int_map.end(); ) // no it++
  {
    const int_mapt::const_iterator b_it=b.int_map.begin();
    if(b_it==b.int_map.end())
    {
      int_mapt::iterator next=it;
      next++; // will go away with C++11, as erase() returns next
      int_map.erase(it);
      it=next;
      result=true;
    }
    else
    {
      if(it->second.join(b_it->second))
        result=true;

      it++;
    }
  }

  for(float_mapt::iterator it=float_map.begin();
      it!=float_map.end(); ) // no it++
  {
    const float_mapt::const_iterator b_it=b.float_map.begin();
    if(b_it==b.float_map.end())
    {
      float_mapt::iterator next=it;
      next++; // will go away with C++11, as erase() returns next
      float_map.erase(it);
      it=next;
      result=true;
    }
    else
    {
      if(it->second.join(b_it->second))
        result=true;

      it++;
    }
  }

  return result;
}        


void interval_mapt::havoc_rec(const exprt &lhs)
{
  if(lhs.id()==ID_if)
  {
    havoc_rec(to_if_expr(lhs).true_case());
    havoc_rec(to_if_expr(lhs).false_case());
  }
  else if(lhs.id()==ID_symbol)
  {
    irep_idt identifier=to_symbol_expr(lhs).get_identifier();

    if(is_int(lhs.type()))
    {
      integer_intervalt &integer_interval(int_map[identifier]);
      integer_interval.lower_set=false;
      integer_interval.upper_set=false;
    }  
    else if(is_float(lhs.type()))
    {
      ieee_float_intervalt &float_interval(float_map[identifier]);
    
      float_interval.lower_set=false;
      float_interval.upper_set=false;
    }
  }
  else if(lhs.id()==ID_typecast)
  {
    havoc_rec(to_typecast_expr(lhs).op());
  }
}

void interval_mapt::assume_rec(const exprt & cond, bool negation)
{
  if(cond.id()==ID_lt || cond.id()==ID_le ||
     cond.id()==ID_gt || cond.id()==ID_ge ||
     cond.id()==ID_equal || cond.id()==ID_notequal)
  {
    assert(cond.operands().size()==2);

    if(negation) // !x<y  ---> x>=y
    {
      if(cond.id()==ID_lt)
        assume_rec(cond.op0(), ID_ge, cond.op1());
      else if(cond.id()==ID_le)
        assume_rec(cond.op0(), ID_gt, cond.op1());
      else if(cond.id()==ID_gt)
        assume_rec(cond.op0(), ID_le, cond.op1());
      else if(cond.id()==ID_ge)
        assume_rec(cond.op0(), ID_lt, cond.op1());
      else if(cond.id()==ID_equal)
        assume_rec(cond.op0(), ID_notequal, cond.op1());
      else if(cond.id()==ID_notequal)
        assume_rec(cond.op0(), ID_equal, cond.op1());
    }
    else
      assume_rec(cond.op0(), cond.id(), cond.op1());
  }
  else if(cond.id()==ID_not)
  {
    assume_rec(to_not_expr(cond).op(), !negation);
  }
  else if(cond.id()==ID_and)
  {
    if(!negation)
      forall_operands(it, cond)
        assume_rec(*it, false);
  }
  else if(cond.id()==ID_or)
  {
    if(negation)
      forall_operands(it, cond)
        assume_rec(*it, true);
  }
}


void interval_mapt::assume_rec(const exprt &lhs, irep_idt id, const exprt &rhs)
{
  if(lhs.id()==ID_typecast)
    return assume_rec(to_typecast_expr(lhs).op(), id, rhs);

  if(rhs.id()==ID_typecast)
    return assume_rec(lhs, id, to_typecast_expr(rhs).op());

  if(id==ID_equal)
  {
    assume_rec(lhs, ID_ge, rhs);
    assume_rec(lhs, ID_le, rhs);
    return;
  }
  
  if(id==ID_ge)
    return assume_rec(rhs, ID_le, lhs);    
    
  if(id==ID_gt)
    return assume_rec(rhs, ID_lt, lhs);    
    
  // we now have lhs <  rhs or
  //             lhs <= rhs


  // [bw] 
  // x!=rhs && x==rhs => bottom
  // x!=rhs && x==y && y==rhs => bottom
  if(id==ID_notequal)
  {
    return;
  }

  if(!(id==ID_lt || id==ID_le))
    throw "unexpected id " + from_expr(lhs) + " " + id2string(id) + " " + from_expr(rhs);

  #ifdef DEBUG  
  std::cout << "   assume_rec: " 
            << from_expr(lhs) << " " << id << " "
            << from_expr(rhs) << "\n";
  #endif
  
  if(lhs.id()==ID_symbol && rhs.id()==ID_constant)
  {
    irep_idt lhs_identifier=to_symbol_expr(lhs).get_identifier();
    
    if(is_int(lhs.type()) && is_int(rhs.type()))
    {
      mp_integer tmp;
      to_integer(rhs, tmp);
      if(id==ID_lt) --tmp;
      int_map[lhs_identifier].make_le_than(tmp);
    }
    else if(is_float(lhs.type()) && is_float(rhs.type()))
    {
      ieee_floatt tmp(to_constant_expr(rhs));
      if(id==ID_lt) tmp.decrement();
      float_map[lhs_identifier].make_le_than(tmp);
    }
  }
  else if(lhs.id()==ID_constant && rhs.id()==ID_symbol)
  {
    irep_idt rhs_identifier=to_symbol_expr(rhs).get_identifier();
    
    if(is_int(lhs.type()) && is_int(rhs.type()))
    {
      mp_integer tmp;
      to_integer(lhs, tmp);
      if(id==ID_lt) ++tmp;
      int_map[rhs_identifier].make_ge_than(tmp);
    }
    else if(is_float(lhs.type()) && is_float(rhs.type()))
    {
      ieee_floatt tmp(to_constant_expr(lhs));
      if(id==ID_lt) tmp.increment();
      float_map[rhs_identifier].make_ge_than(tmp);
    }
  }
  else if(lhs.id()==ID_symbol && rhs.id()==ID_symbol)
  {
    irep_idt lhs_identifier=to_symbol_expr(lhs).get_identifier();
    irep_idt rhs_identifier=to_symbol_expr(rhs).get_identifier();
    
    if(is_int(lhs.type()) && is_int(rhs.type()))
    {
      integer_intervalt &lhs_i=int_map[lhs_identifier];
      integer_intervalt &rhs_i=int_map[rhs_identifier];
      lhs_i.meet(rhs_i);
      rhs_i=lhs_i;
    }
    else if(is_float(lhs.type()) && is_float(rhs.type()))
    {
      ieee_float_intervalt &lhs_i=float_map[lhs_identifier];
      ieee_float_intervalt &rhs_i=float_map[rhs_identifier];
      lhs_i.meet(rhs_i);
      rhs_i=lhs_i;
    }
  }
  else if(lhs.id()==ID_symbol)
  {
    irep_idt lhs_identifier=to_symbol_expr(lhs).get_identifier();
  
    int_replace_mapt int_replace_map;
    float_replace_mapt float_replace_map;
    
    eval_rec(rhs, int_replace_map, float_replace_map);
    
    if(is_int(rhs.type()))
    {
      const integer_intervalt &integer_interval=int_replace_map[rhs];
      mp_integer tmp=integer_interval.upper;
      if(id==ID_lt) ++tmp;
      int_map[lhs_identifier].make_le_than(tmp);
    }
    else if(is_float(rhs.type()))
    {
      const ieee_float_intervalt &float_interval=float_replace_map[rhs];
      ieee_floatt tmp(float_interval.upper);
      if(id==ID_lt) tmp.increment();
      float_map[lhs_identifier].make_le_than(tmp);
    }
  }
  else if(rhs.id()==ID_symbol)
  {
    irep_idt rhs_identifier=to_symbol_expr(rhs).get_identifier();
  
    int_replace_mapt int_replace_map;
    float_replace_mapt float_replace_map;
    
    eval_rec(lhs, int_replace_map, float_replace_map);
    
    if(is_int(lhs.type()))
    {
      const integer_intervalt &integer_interval=int_replace_map[lhs];
      mp_integer tmp=integer_interval.lower;
      if(id==ID_lt) ++tmp;
      int_map[rhs_identifier].make_ge_than(tmp);
    }
    else if(is_float(lhs.type()))
    {
      const ieee_float_intervalt &float_interval=float_replace_map[lhs];
      ieee_floatt tmp(float_interval.lower);
      if(id==ID_lt) tmp.increment();
      float_map[rhs_identifier].make_ge_than(tmp);
    }
  }
  
}
              

// interval arithmetic -- move this into the interval_template data structure
template<typename T>
interval_templatet<T> make_plus(const std::vector<interval_templatet<T> > & operands)
{
  interval_templatet<T> result;
  
  bool lower_set=true;
  
  for(unsigned i=0; i<operands.size(); ++i)
  {
    lower_set=lower_set && operands[i].lower_set;
  }
  
  bool upper_set=true;
  
  for(unsigned i=0; i<operands.size(); ++i)
  {
    upper_set=upper_set && operands[i].upper_set;
  }

  if(lower_set)
  {
    T lower=operands[0].lower;
    
    for(unsigned i=1; i<operands.size(); ++i)
    {
      lower+=operands[i].lower;
    }
    
    result.make_ge_than(lower);
  }
  
  if(upper_set)
  {
    T upper=operands[0].upper;
    
    for(unsigned i=1; i<operands.size(); ++i)
    {
      upper+=operands[i].upper;
    }
    
    result.make_le_than(upper);
  }
  
  return result;
}



void interval_mapt::eval_rec(const exprt& expr, 
                             int_replace_mapt& int_replace_map, 
                             float_replace_mapt& float_replace_map)
{
  if(expr.id()==ID_constant)
  {
    //
    if(is_int(expr.type()))
    {
      mp_integer constant;
      to_integer(expr, constant);
      int_replace_map[expr]=integer_intervalt(constant);
    }
    else if(is_float(expr.type()) && is_float(expr.type()))
    {
      ieee_floatt constant(to_constant_expr(expr));
    
      float_replace_map[expr]=ieee_float_intervalt(constant);
    }
  }

  else

  if(expr.id()==ID_symbol)
  {
    // look up the symbol in the interval map
    irep_idt identifier=to_symbol_expr(expr).get_identifier();
    
    if(is_int(expr.type()))
    {
      int_replace_map[expr]=int_map[identifier];
    }
    else if(is_float(expr.type()) && is_float(expr.type()))
    {
      float_replace_map[expr]=float_map[identifier];
    }
  }
  
  else 
  
  if(   expr.id()==ID_plus 
     || expr.id()==ID_minus
     || expr.id()==ID_mult)
  {
    // recursively evaluate subexpressions
    forall_operands(it, expr)
      eval_rec(*it, int_replace_map, float_replace_map);

    // carry out the arithmetic operation
    if(is_int(expr.type()))
    {
      // fetch the operands
      const exprt::operandst &operands=expr.operands();
      std::vector<integer_intervalt> interval_operands;
      
      for(unsigned i=0; i<operands.size(); ++i)
      {
        interval_operands.push_back(int_replace_map[operands[i]]);
      }      

      if(expr.id()==ID_plus)
      {
        assert(operands.size()==2);
        int_replace_map[expr]=make_plus(interval_operands);
      }
            
      
          
    }
  }

  else
  
  if(expr.id()==ID_typecast)
  {
    // potential conversion between interval types
  }

  

}
              
              

