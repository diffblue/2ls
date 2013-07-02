/*******************************************************************\

Module: Delta Checking Solver

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_DELTACHECK_SOLVER_H
#define CPROVER_DELTACHECK_SOLVER_H

#include <util/decision_procedure.h>
#include <util/union_find.h>

class solvert:public decision_proceduret
{
public:
  // standard solver interface
  
  explicit solvert(const namespacet &_ns);

  virtual exprt get(const exprt &expr) const;
  virtual void print_assignment(std::ostream &out) const;
  virtual void set_to(const exprt &expr, bool value);
  
  virtual resultt dec_solve();

  virtual std::string decision_procedure_text() const
  {
    return "DeltaCheck equality+UF solver";
  }
  
protected:
  inline void set_equal(const exprt &a, const exprt &b)
  {
    set_equal(add(a), add(b));
  }

  inline void set_equal(unsigned a, unsigned b)
  {
    equalities.make_union(a, b);
  }
  
  // a numbering for expressions
  numbering<exprt> expr_numbering;

  // equality logic
  unsigned_union_find equalities;
  
  struct solver_ift
  {
    unsigned cond, true_case, false_case, e_nr;
  };
  
  typedef std::vector<solver_ift> if_listt;
  if_listt if_list;
  
  struct solver_uft
  {
    unsigned e_nr;
  };
  
  typedef std::vector<solver_uft> uf_listt;
  uf_listt uf_list;
  
  struct solver_ort
  {
    unsigned op0, op1, e_nr;
  };

  typedef std::vector<solver_ort> or_listt;
  or_listt or_list;
  
  struct solver_andt
  {
    unsigned op0, op1, e_nr;
  };

  typedef std::vector<solver_andt> and_listt;
  and_listt and_list;
  
  void add(unsigned nr);

  unsigned add(const exprt &expr)
  {
    unsigned old_size=expr_numbering.size();
    unsigned nr=expr_numbering(expr);
    if(expr_numbering.size()!=old_size) add(nr);
    return nr;
  }
  
  unsigned false_nr, true_nr;
  
  inline bool is_equal(unsigned a, unsigned b)
  {
    return equalities.find(a)==equalities.find(b);
  }
};

#endif
