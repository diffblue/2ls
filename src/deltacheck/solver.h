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
  
  inline void set_equal(const exprt &a, const exprt &b)
  {
    set_equal(add(a), add(b));
  }

  inline bool is_equal(const exprt &a, const exprt &b) const
  {
    unsigned a_nr, b_nr;
    if(expr_numbering.get_number(a, a_nr)) return false;
    if(expr_numbering.get_number(b, b_nr)) return false;
    return is_equal(a_nr, b_nr);
  }

  unsigned add(const exprt &expr)
  {
    unsigned old_size=expr_numbering.size();
    unsigned nr=expr_numbering(expr);
    if(expr_numbering.size()!=old_size) add(nr);
    return nr;
  }
  
protected:
  inline void set_equal(unsigned a, unsigned b)
  {
    equalities.make_union(a, b);
  }
  
  inline bool implies_equal(unsigned a, unsigned b)
  {
    if(is_equal(a, b)) return false; // no progres
    equalities.make_union(a, b);
    return true; // progress!
  }
  
  // a numbering for expressions
  numbering<exprt> expr_numbering;

  // equality logic
  unsigned_union_find equalities;
  
  struct solver_exprt
  {
    unsigned e_nr;
    std::vector<unsigned> op;
  };
  
  typedef std::vector<solver_exprt> solver_expr_listt;
  solver_expr_listt if_list, or_list, and_list;
  
  typedef std::map<irep_idt, solver_expr_listt> uf_mapt;
  uf_mapt uf_map;
  
  solver_exprt convert(unsigned nr);
  
  void add(unsigned nr);

  unsigned false_nr, true_nr;
  
  inline bool is_equal(unsigned a, unsigned b) const
  {
    return equalities.find(a)==equalities.find(b);
  }
};

#endif
