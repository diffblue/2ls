/*******************************************************************\

Module: Delta Checking Solver

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_DELTACHECK_SOLVER_H
#define CPROVER_DELTACHECK_SOLVER_H

#include <util/decision_procedure.h>
#include <util/union_find.h>
#include <util/expanding_vector.h>

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

  // add an expression, returns its handle
  unsigned add(const exprt &expr)
  {
    unsigned old_size=expr_numbering.size();
    unsigned nr=expr_numbering(expr);
    if(expr_numbering.size()!=old_size) new_expression(nr);
    return nr;
  }
  
protected:
  // make 'a' and 'b' equal
  inline void set_equal(unsigned a, unsigned b)
  {
    equalities.make_union(a, b);
  }

  // make 'a' and 'b' equal, and return 'true'
  // iff this wasn't the case before
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
  
  // further data per expression
  struct solver_exprt
  {
    // the numbers of the operands
    std::vector<unsigned> op;
  };
  
  typedef expanding_vector<solver_exprt> expr_mapt;
  expr_mapt expr_map;

  // lists of expressions with particular IDs  
  typedef std::vector<unsigned> solver_expr_listt;
  solver_expr_listt if_list, or_list, and_list, not_list;

  // uninterpreted functions (and predicates), mapping
  // expression id -> to the list of expressions of this kind  
  typedef std::map<irep_idt, solver_expr_listt> uf_mapt;
  uf_mapt uf_map;

  // builds above solver_exprt for given expression  
  solver_exprt build_solver_expr(unsigned nr);

  // called to recurse over the operands of a new expression
  void add_operands(unsigned nr);

  // called after new expresion with given number has been added
  void new_expression(unsigned nr);

  // handy numbers of well-known constants
  unsigned false_nr, true_nr;
  
  inline bool is_equal(unsigned a, unsigned b) const
  {
    return equalities.find(a)==equalities.find(b);
  }
};

#endif
