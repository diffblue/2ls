/*******************************************************************\

Module: Predicates

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_DELTACHECK_PREDICATES_H
#define CPROVER_DELTACHECK_PREDICATES_H

#include <expr.h>
#include <namespace.h>

#include <cuddObj.hh>

struct predicatet
{
  irep_idt id;
  exprt expr;
  
  // the BDD variable for the predicate and the next-state version
  BDD var, next_var;
  
  std::string string;
};

class predicatest
{
public:
  explicit predicatest(const namespacet &_ns):ns(_ns)
  {
  }

  typedef std::vector<predicatet> predicate_vectort;
  typedef std::map<exprt, unsigned> predicate_mapt;
  predicate_vectort predicate_vector;
  predicate_mapt predicate_map;
  
  inline unsigned size() const
  {
    return (unsigned)predicate_vector.size();
  }
  
  void add(Cudd &mgr, const exprt &src);
  
  std::string make_list() const;
  
  const predicatet &operator[] (std::size_t i) const
  {
    return predicate_vector[i];
  }
  
protected:
  const namespacet &ns;
}; 

#endif
