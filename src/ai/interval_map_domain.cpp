#include <goto-programs/goto_functions.h>

#include "interval_map_domain.h"
                     
                     
interval_map_domaint::~interval_map_domaint()
{
}

                            
interval_mapt interval_map_domaint::transform(const interval_mapt &v,
                                const ssa_cfg_concrete_transformert &t)
{
  interval_mapt result(v);

  for(unsigned i=0; i<t.equalities.size(); ++i)
  {
    const equal_exprt &equal=t.equalities[i];
    result.assume_rec(equal.op0(), ID_equal, equal.op1());
  }

  for(unsigned i=0; i<t.constraints.size(); ++i)
  {
    const exprt &constraint=t.constraints[i];
    result.assume_rec(constraint);
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
    
    if(!interval.upper_set)
      out << "INF";
    else
      out << interval.upper;
    out << "] ";  
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
    out << "] ";
  }
}


