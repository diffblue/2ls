/*******************************************************************\

Module: Second-order formula

Author: Peter Schrammel

\*******************************************************************/

#ifndef CPROVER_2LS_SO_FORMULA_H
#define CPROVER_2LS_SO_FORMULA_H

#include <util/std_expr.h>
#include "predicate.h"

class so_formulat : public exprt 
{
public:
  bool is_well_formed();
  predicate_symbol_sett bound_predicates();
  predicate_symbol_sett free_predicates(
    const predicate_symbol_sett &bound_predicates);

protected:
  void bound_predicates_rec(
    const exprt& expr, 
    predicate_symbol_sett& s);
  void free_predicates_rec(
    const exprt& expr, 
    const predicate_symbol_sett &bound_predicates,
    predicate_symbol_sett& s);
};

typedef std::vector<so_formulat> so_formulaet;

extern inline so_formulat &to_so_formula(exprt &expr)
{
  return static_cast<so_formulat &>(expr);
}

extern inline const so_formulat &to_so_formula(const exprt &expr)
{
  return static_cast<const so_formulat &>(expr);
}

#endif
