/*******************************************************************\

Module: Delta Checking Solver

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_DELTACHECK_SOLVER_H
#define CPROVER_DELTACHECK_SOLVER_H

#include <set>

#include <util/decision_procedure.h>
#include <util/union_find.h>
#include <util/expanding_vector.h>

#include <analyses/intervals.h>

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

  bool is_equal(const exprt &a, const exprt &b) const;
  
  inline void add_expression(const exprt &expr)
  {
    add(expr);
  }

protected:
  void set_to_rec(const exprt &expr, bool value);
  
  // simplify and add expression, return its handle
  unsigned add(const exprt &expr);

  // recursively add a simplified expression, returns its handle
  unsigned add_rec(const exprt &expr);

  // make 'a' and 'b' equal
  inline void set_equal(unsigned a, unsigned b)
  {
    equalities.make_union(a, b);
  }

  // make 'a' and 'b' equal, and track if
  // this wasn't the case before
  inline void implies_equal(unsigned a, unsigned b, bool &progress)
  {
    if(is_equal(a, b)) return; // no progres
    equalities.make_union(a, b);
    progress=true; // progress!
  }
  
  // add a bound, and track if this is a new bound
  enum weak_strictt { WEAK, STRICT };
  enum lower_uppert { LOWER, UPPER };
  
  void bound(const constant_exprt &bound,
             const exprt &what,
             weak_strictt weak_strict,
             lower_uppert lower_upper,
             bool &progress);
  
  // a numbering for expressions
  numbering<exprt> expr_numbering;

  // equality logic
  unsigned_union_find equalities;
  
  inline bool is_equal(unsigned a, unsigned b) const
  {
    return equalities.find(a)==equalities.find(b);
  }
  
  // disequalities; the smaller index is the key
  typedef std::map<unsigned, std::set<unsigned> > disequalitiest;
  disequalitiest disequalities;
  
  inline bool is_disequal(unsigned a, unsigned b) const
  {
    if(a>b) std::swap(a, b);
    disequalitiest::const_iterator it=disequalities.find(a);
    if(it==disequalities.end()) return false;
    return it->second.find(b)!=it->second.end();
  }

  void set_disequal(unsigned a, unsigned b)
  {
    if(a>b) std::swap(a, b);
    disequalities[a].insert(b);
  }

  // further data per expression
  struct solver_exprt
  {
    // the numbers of the operands
    std::vector<unsigned> op;
    
    bool predicate_processed;
    
    solver_exprt():predicate_processed(false)
    {
    }
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
  
  inline bool is_true(unsigned a) const
  {
    return is_equal(a, true_nr);
  }

  inline bool is_false(unsigned a) const
  {
    return is_equal(a, false_nr);
  }

  // interval domain
  typedef expanding_vector<integer_intervalt> integer_intervalst;
  typedef expanding_vector<ieee_float_intervalt> ieee_float_intervalst;
  ieee_float_intervalst ieee_float_intervals;
  integer_intervalst integer_intervals;
};

#endif
