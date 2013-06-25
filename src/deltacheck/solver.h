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
  explicit solvert(const namespacet &_ns):decision_proceduret(_ns)
  {
  }

  virtual exprt get(const exprt &expr) const;
  virtual void print_assignment(std::ostream &out) const;
  virtual void set_to(const exprt &expr, bool value);
  
  virtual resultt dec_solve()
  {
    return D_ERROR;
  }

  virtual std::string decision_procedure_text() const
  {
    return "DeltaCheck equality+UF solver";
  }
  
  void set_equal(const exprt &, const exprt &);

  // special feature for data-flow analyses
  typedef std::vector<exprt> var_sett;
  typedef std::list<var_sett> src_listt;

  // Find facts true over all source sets,
  // and adds these as constraints for the destination.
  // Returns true iff anything new was implied.
  bool join(const src_listt &src,
            const var_sett &dest);

protected:

  // a numbering for expressions
  numbering<exprt> expr_numbering;

  // equality logic
  unsigned_union_find equalities;
};

#endif
