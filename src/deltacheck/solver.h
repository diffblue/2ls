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
  
  explicit solvert(const namespacet &_ns):decision_proceduret(_ns)
  {
  }

  virtual exprt get(const exprt &expr) const;
  virtual void print_assignment(std::ostream &out) const;
  virtual void set_to(const exprt &expr, bool value);
  
  virtual resultt dec_solve();

  virtual std::string decision_procedure_text() const
  {
    return "DeltaCheck equality+UF solver";
  }
  
  // special feature for data-flow analyses
  typedef std::vector<symbol_exprt> var_listt;

  struct predicatet
  {
    symbol_exprt guard;
    var_listt vars;

    void output(std::ostream &) const;
    void make_false();
    
    // returns 'true' iff predicate is weakened
    bool disjunction(const predicatet &);
    
    // rename supporting set of variables
    void rename(
      const symbol_exprt &new_guard,
      const var_listt &new_vars);
  };
  
  friend inline std::ostream & operator << (
    std::ostream &out, const predicatet &predicate)
  {
    predicate.output(out);
    return out;
  }

  void set_to_true(const predicatet &);
  void get(predicatet &);

protected:
  void set_equal(const exprt &, const exprt &);

  // a numbering for expressions
  numbering<exprt> expr_numbering;

  // equality logic
  unsigned_union_find equalities;
};

#endif
