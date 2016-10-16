/*******************************************************************\

Module: Second order formula

Author: Peter Schrammel

\*******************************************************************/

#ifndef CPROVER_2LS_SO_FORMULA_H
#define CPROVER_2LS_SO_FORMULA_H

#include <util/std_expr.h>

class so_formulat : public exprt 
{
public:
  bool is_well_formed();
};

extern inline so_formulat &to_so_formula(exprt &expr)
{
  return static_cast<so_formulat &>(expr);
}

extern inline const so_formulat &to_so_formula(const exprt &expr)
{
  return static_cast<const so_formulat &>(expr);
}

#endif
