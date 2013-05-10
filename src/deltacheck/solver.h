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
  
protected:
  void set_equal(const exprt &, const exprt &);
};

#endif
