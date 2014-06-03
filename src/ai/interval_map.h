#ifndef CPROVER_INTERVAL_MAP_H
#define CPROVER_INTERVAL_MAP_H

#include <analyses/intervals.h>

class interval_mapt
{
public:
  typedef std::map<irep_idt, integer_intervalt> int_mapt;
  typedef std::map<irep_idt, ieee_float_intervalt> float_mapt;

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
  
};

#endif
