/*******************************************************************\

Module: Delta Checking Solver

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_SOLVER_H
#define CPROVER_SOLVER_H

#include <util/decision_procedure.h>

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
    return "DeltaCheck equalit solver";
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
};

#endif
