/*******************************************************************\

Module: Intervals

Author: Bjorn Wachter

\*******************************************************************/

#ifndef CPROVER_INTERVAL_MAP_H
#define CPROVER_INTERVAL_MAP_H

#include <analyses/intervals.h>

class interval_mapt
{
public:
  typedef hash_map_cont<irep_idt, integer_intervalt, irep_id_hash> int_mapt;
  typedef hash_map_cont<irep_idt, ieee_float_intervalt, irep_id_hash> float_mapt;

  int_mapt int_map;
  float_mapt float_map;

  bool join(const interval_mapt &b);
  bool meet(const interval_mapt &b);
  bool is_leq(const interval_mapt &b);

  // auxiliary functions for abstract transformer
  void havoc_rec(const exprt &);
    
  void assume_rec(const exprt &, bool negation=false);
  void assume_rec(const exprt &lhs, irep_idt id, const exprt &rhs);
  
  
  
  static bool is_int(const typet &src)
  {
    return src.id()==ID_signedbv || src.id()==ID_unsignedbv;
  }
  
  static bool is_float(const typet &src)
  {
    return src.id()==ID_floatbv;
  }

protected:
  // expression evaluation
  typedef std::map<exprt, integer_intervalt> int_replace_mapt;
  typedef std::map<exprt, ieee_float_intervalt> float_replace_mapt;
  
  // final result to be found in int_replace_map[expr] or in float_replace_map[expr]
  void eval_rec(const exprt& expr, 
                int_replace_mapt& int_replace_map, 
                float_replace_mapt& float_replace_map);
};

#endif
