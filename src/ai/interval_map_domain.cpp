/*******************************************************************\

Module: Interval domain

Author: Bjorn Wachter

\*******************************************************************/

#include <goto-programs/goto_functions.h>

#include "interval_map_domain.h"
                     



void interval_map_domaint::initialise(interval_mapt& result, const concrete_transformerst &transformers)
{
  typedef concrete_transformerst::symbols_sett symbols_sett;

  // set free symbols to top
  for(symbols_sett::const_iterator 
      it=transformers.free_symbols.begin();
      it!=transformers.free_symbols.end();
      ++it)
  {
    const symbol_exprt &symbol_expr=*it;
       
    const irep_idt &id=symbol_expr.get_identifier();
    
    if(is_int(symbol_expr.type()))
    {
      result.int_map[id].lower_set=false;
      result.int_map[id].upper_set=false;
    }
    else if(is_float(symbol_expr.type()))
    {
      result.float_map[id].lower_set=false;
      result.float_map[id].upper_set=false;
    }
    
  }
  
  // set bound symbols to bottom
  for(symbols_sett::const_iterator 
      it=transformers.bound_symbols.begin();
      it!=transformers.bound_symbols.end();
      ++it)
  {
    const symbol_exprt &symbol_expr=*it;
    const irep_idt &id=symbol_expr.get_identifier();
    
    if(is_int(symbol_expr.type()))
    {
      mp_integer zero(0), one(1);
      result.int_map[id].set_lower(one);
      result.int_map[id].set_upper(zero);
    } if(is_float(symbol_expr.type()))
    {
      ieee_floatt zero;
      zero.from_float(0.0);
      ieee_floatt one;
      one.from_float(1.0);
      result.float_map[id].set_lower(one);
      result.float_map[id].set_upper(zero);   
    }
  }
}


                     
interval_map_domaint::~interval_map_domaint()
{
}

                            
interval_mapt interval_map_domaint::transform(const interval_mapt &v,
                                const concrete_transformert &t)
{
  interval_mapt result(v);
  
  if(t.is_equality())
  {
    const exprt &lhs=t.lhs();
    const exprt &rhs=t.rhs();
    assume_rec(lhs, ID_equal, rhs)
  }
  else
  {
    const exprt &expr=t.expr();
    assume_rec(expr)
  }
  
  return result;
}                                


                            
bool interval_map_domaint::widen(interval_mapt &v1, 
                                 const interval_mapt &v2)
{
 
  bool result=false;
 
  for(interval_mapt::int_mapt::iterator 
      it=v1.int_map.begin();
      it!=v1.int_map.end(); ++it) 
  {
    const irep_idt &var=it->first;
  
    integer_intervalt &interval1=it->second;
    
    integer_intervalt interval2;
    
    interval_mapt::int_mapt::const_iterator it2=v2.int_map.find(var);
    
    if(it2!=v2.int_map.end())
      interval2=it2->second;
         
    // lower bound
    if(interval2.lower<interval1.lower || !interval2.lower_set)
      interval1.make_le_than(interval_widening_thresholds.lower_bound(var, interval2.lower, interval1.lower_set));
    
    result=result && (!interval1.lower_set || (interval2.upper_set && interval1.lower <= interval2.lower));
    
    // upper bound
    if(interval2.lower>interval1.lower || !interval2.upper_set)
      interval1.make_ge_than(interval_widening_thresholds.upper_bound(var, interval2.upper, interval1.upper_set));
      
    result=result && (!interval1.upper_set || (interval2.upper_set && interval1.upper >= interval2.upper));
  }
  
  for(interval_mapt::float_mapt::iterator 
      it=v1.float_map.begin();
      it!=v1.float_map.end(); ++it) 
  {
    const irep_idt &var=it->first;
  
    ieee_float_intervalt &interval1=it->second;
    
    ieee_float_intervalt interval2;
    
    interval_mapt::float_mapt::const_iterator it2=v2.float_map.find(var);
    
    if(it2!=v2.float_map.end())
      interval2=it2->second;
         
    // lower bound
    if(interval2.lower<interval1.lower || !interval2.lower_set)
      interval1.make_le_than(interval_widening_thresholds.lower_bound(var, interval2.lower, interval1.lower_set));
    
    result=result && (!interval1.lower_set || (interval2.upper_set && interval1.lower <= interval2.lower));
    
    // upper bound
    if(interval2.lower>interval1.lower || !interval2.upper_set)
      interval1.make_ge_than(interval_widening_thresholds.upper_bound(var, interval2.upper, interval1.upper_set));
      
    result=result && (!interval1.upper_set || (interval2.upper_set && interval1.upper >= interval2.upper));  
  }
 
  return result;
}                            


void interval_map_domaint::output(const interval_mapt &v, std::ostream& out)
{


  for(interval_mapt::int_mapt::const_iterator 
      it=v.int_map.begin();
      it!=v.int_map.end(); ++it)
  {
    const irep_idt &var=it->first;
    
    const integer_intervalt &interval=it->second;

    out << id2string(var) << " : [" ;
        
    if(!interval.lower_set)
      out << "-INF";
    else
      out << interval.lower;
    
    out << ",";
    
    if(!interval.upper_set)
      out << "INF";
    else
      out << interval.upper;
    out << "]\n";  
  }  

  for(interval_mapt::float_mapt::const_iterator 
      it=v.float_map.begin();
      it!=v.float_map.end(); ++it) 
  {
    const irep_idt &var=it->first;
    
    const ieee_float_intervalt &interval=it->second;

    out << id2string(var) << " : [" ;
    
    if(!interval.lower_set)
      out << "-INF";
    else
      out << interval.lower;
    
    if(!interval.upper_set)
      out << "INF";
    else
      out << interval.upper;    
    out << "]\n";
  }
}


