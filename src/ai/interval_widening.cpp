#include <goto-programs/goto_functions.h>

#include "interval_map.h"
#include "interval_widening.h"




mp_integer interval_widening_thresholdst::upper_bound(const irep_idt &var, const mp_integer &m, bool &is_set)
{
  int_thresholds_mapt::iterator threshold_map_it=int_thresholds_map.find(var);
  
  // fall back
  if(threshold_map_it==int_thresholds_map.end())
  {
    if(m>int_default_upper_threshold)
      is_set=false;
  }
  else
  {
    int_thresholdst int_thresholds=threshold_map_it->second;
    for(int_thresholdst::const_iterator
        thresh_it=int_thresholds.begin();
        thresh_it!=int_thresholds.end();
        ++thresh_it)
    {
      if(m < *thresh_it)
        return *thresh_it;
    }
    
    is_set=false;    
  }
  
  return int_default_upper_threshold;
}

mp_integer interval_widening_thresholdst::lower_bound(const irep_idt &var, const mp_integer &m, bool &is_set)
{
  int_thresholds_mapt::iterator threshold_map_it=int_thresholds_map.find(var);
  
  // fall back
  if(threshold_map_it==int_thresholds_map.end())
  {
    if(m<int_default_upper_threshold)
      is_set=false;
  }
  else
  {
    int_thresholdst int_thresholds=threshold_map_it->second;
    for(int_thresholdst::const_reverse_iterator
        thresh_it=int_thresholds.rbegin();
        thresh_it!=int_thresholds.rend();
        ++thresh_it)
    {
      if(m > *thresh_it)
        return *thresh_it;
    }
    
    is_set=false;    
  }
  
  return int_default_lower_threshold;
}

ieee_floatt interval_widening_thresholdst::lower_bound(const irep_idt &var, const ieee_floatt &f, bool &is_set)
{
  float_thresholds_mapt::iterator threshold_map_it=float_thresholds_map.find(var);
  
  // fall back
  if(threshold_map_it==float_thresholds_map.end())
  {
    if(f<float_default_upper_threshold)
      is_set=false;
  }
  else
  {
    float_thresholdst float_thresholds=threshold_map_it->second;
    for(float_thresholdst::const_reverse_iterator
        thresh_it=float_thresholds.rbegin();
        thresh_it!=float_thresholds.rend();
        ++thresh_it)
    {
      if(f > *thresh_it)
        return *thresh_it;
    }
    
    is_set=false;    
  }
  
  return float_default_lower_threshold;
}

ieee_floatt interval_widening_thresholdst::upper_bound(const irep_idt &var, const ieee_floatt &f, bool &is_set)
{

  float_thresholds_mapt::iterator threshold_map_it=float_thresholds_map.find(var);
  
  // fall back
  if(threshold_map_it==float_thresholds_map.end())
  {
    if(f>float_default_upper_threshold)
      is_set=false;
  }
  else
  {
    float_thresholdst float_thresholds=threshold_map_it->second;
    for(float_thresholdst::const_iterator
        thresh_it=float_thresholds.begin();
        thresh_it!=float_thresholds.end();
        ++thresh_it)
    {
      if(f < *thresh_it)
        return *thresh_it;
    }
    
    is_set=false;    
  }
  
  return float_default_upper_threshold;
}

