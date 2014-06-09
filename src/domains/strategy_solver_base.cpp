#include <set>
#include <cmath>

#include <util/i2string.h>

#include "strategy_solver_base.h"

bool strategy_solver_baset::improve(const invariantt &inv, strategyt &strategy)
{
  solver << template_domain.to_constraints(inv); //TODO: add assumption literal
  exprt c = template_domain.to_not_constraints(inv); //TODO: add assumption literal
  instrument_template_rows(c);
  solver << c; //TODO: add assumption literal
  bool first = true;
  while(true)
  {
    if(solver() == decision_proceduret::D_SATISFIABLE) 
    { 
      template_domaint::rowt row = get_template_row();
      strategy.push_back(row);
      solver << get_blocking_constraint(row); //TODO: add assumption literal
    }
    else if(first) return false;
    first = false;
  }
}



void strategy_solver_baset::instrument_template_rows(exprt &expr)
{
  assert(expr.id()==ID_or);
  assert(expr.operands().size()==template_domain.template_size());
  strategy_literals.clear();
  unsigned sl_size = ceil(log2(expr.operands().size()));
  strategy_literals.reserve(sl_size);
  for(unsigned i = 0; i<sl_size; i++)
  {
    strategy_literals[i] = solver.convert(
      symbol_exprt("strategy$"+i2string(i), bool_typet()));
  }
  for(unsigned d = 0; d<expr.operands().size(); d++)
  {
    exprt::operandst c;
    c.reserve(sl_size+1);
    c.push_back(expr.operands()[d]);
    encode_row(d,c);
    expr.operands()[d] = conjunction(c);
  }
}

template_domaint::rowt strategy_solver_baset::get_template_row()
{
  template_domaint::rowt row = 0;
  for(unsigned i=0;i<strategy_literals.size(); i++, row <<= 1)
  {
    if(solver.l_get(strategy_literals[strategy_literals.size()-i-1]).is_true()) 
    {
      row |= 1;
    }
  }
  return row;
}

exprt strategy_solver_baset::get_blocking_constraint(template_domaint::rowt row)
{
  exprt::operandst c;
  c.reserve(strategy_literals.size());
  encode_row(row,c);
  return not_exprt(conjunction(c));
}

void strategy_solver_baset::encode_row(template_domaint::rowt row, 
  exprt::operandst &c)
{
  for(unsigned i=0;i<strategy_literals.size(); i++, row >>= 1)
  {
    if(row&1) c.push_back(literal_exprt(strategy_literals[i]));
    else c.push_back(literal_exprt(!strategy_literals[i]));
  }
}
