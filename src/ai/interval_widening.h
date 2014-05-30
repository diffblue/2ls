#ifndef CPROVER_INTERVAL_WIDENING_H
#define CPROVER_INTERVAL_WIDENING_H

#include "interval_map.h"

/*
 Widening thresholds
 */
class interval_widening_thresholdst
{
public: 
  interval_widening_thresholdst()
  : int_default_lower_threshold(-10),
    int_default_upper_threshold(10)
  {
    float_default_lower_threshold.from_float(-10.);
    float_default_upper_threshold.from_float(10.);
  }
  
  // we fall back onto these if no variable-specific thresholds are defined
  mp_integer int_default_lower_threshold;
  mp_integer int_default_upper_threshold;
  ieee_floatt float_default_lower_threshold;
  ieee_floatt float_default_upper_threshold;

  // variable-specific thresholds 
  typedef std::vector<mp_integer> int_thresholdst;
  typedef std::vector<ieee_floatt> float_thresholdst;
  typedef std::map<irep_idt, int_thresholdst> int_thresholds_mapt;
  typedef std::map<irep_idt, float_thresholdst> float_thresholds_mapt;

  
  int_thresholds_mapt int_thresholds_map;
  float_thresholds_mapt float_thresholds_map;
  
  mp_integer upper_bound(const irep_idt &var, const mp_integer &m, bool &is_set);
  ieee_floatt upper_bound(const irep_idt &var, const ieee_floatt &f, bool &is_set);
  
  mp_integer lower_bound(const irep_idt &var, const mp_integer &m, bool &is_set);
  ieee_floatt lower_bound(const irep_idt &var, const ieee_floatt &f, bool &is_set);
protected:
};

#endif
