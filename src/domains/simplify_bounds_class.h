/*******************************************************************\

Module: Bounds Simplification

Author: Peter Schrammel

\*******************************************************************/

#ifndef CPROVER_SIMPLIFY_BOUNDS_CLASS_H
#define CPROVER_SIMPLIFY_BOUNDS_CLASS_H

#include <util/std_types.h>
#include <util/arith_tools.h>

class exprt;
class namespacet;

class simplify_boundst
{
public:
  explicit simplify_boundst(const namespacet &_ns):
    ns(_ns)
  {
  }

  virtual ~simplify_boundst()
  {
  }

  // These below all return 'true' if the simplification wasn't applicable.
  // If false is returned, the expression has changed.

  virtual bool operator()(exprt &expr);
 
  inline static bool is_bitvector_type(const typet &type)
  {
    return type.id()==ID_unsignedbv ||
           type.id()==ID_signedbv;
  }
  inline static mp_integer get_largest(const typet &type)
  {
    if(type.id()==ID_signedbv) return to_signedbv_type(type).largest();
    else if(type.id()==ID_unsignedbv) return to_unsignedbv_type(type).largest();
    assert(false);
  }
  inline static mp_integer get_smallest(const typet &type)
  {
    if(type.id()==ID_signedbv) return to_signedbv_type(type).smallest();
    else if(type.id()==ID_unsignedbv) return to_unsignedbv_type(type).smallest();
    assert(false);
  }

protected:
  const namespacet &ns;

  bool simplify_rec(exprt &expr);
  bool get_min_bound(const exprt &expr, mp_integer &value);
  bool get_max_bound(const exprt &expr, mp_integer &value);

  bool clean_up_implications(exprt &expr);
  bool regroup_implications(exprt &expr);
  bool clean_up_typecast(exprt &expr, const mp_integer &value);

};

#endif
