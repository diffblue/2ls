/*******************************************************************\

Module: Transformer Simplification

Author: Peter Schrammel

\*******************************************************************/

#ifndef CPROVER_SIMPLIFY_TRANSFORMER_CLASS_H
#define CPROVER_SIMPLIFY_TRANSFORMER_CLASS_H

#include <util/type.h>
#include <util/replace_expr.h>

class exprt;
class namespacet;

class simplify_transformert
{
public:
  explicit simplify_transformert(const namespacet &_ns,
				const std::set<irep_idt> &_frozen_symbols):
    ns(_ns),
    frozen_symbols(_frozen_symbols)
  {
  }

  virtual ~simplify_transformert()
  {
  }

  // These below all return 'true' if the simplification wasn't applicable.
  // If false is returned, the expression has changed.

  // main recursion
  bool simplify_rec(exprt &expr, replace_mapt &substitutions);
  
  virtual bool operator()(exprt &expr);
 
  inline static bool is_bitvector_type(const typet &type)
  {
    return type.id()==ID_unsignedbv ||
           type.id()==ID_signedbv ||
           type.id()==ID_bv;
  }
  
protected:
  const namespacet &ns;
  const std::set<irep_idt> &frozen_symbols;

  void collect_node(
    const exprt &expr, replace_mapt &substitutions,
    bool frozen_only,
    bool make_copy);
  bool simplify_node(exprt &expr, const replace_mapt &substitutions);

};

#endif
