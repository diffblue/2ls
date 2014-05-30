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
      int_map.erase(identifier);
    else if(is_float(lhs.type()))
      float_map.erase(identifier);
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
  std::cout << "assume_rec: " 
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
}
              

