#include "predabs_domain.h"
#include "util.h"

#include <iostream>

#include <util/find_symbols.h>
#include <util/prefix.h>
#include <util/i2string.h>
#include <util/simplify_expr.h>
#include <langapi/languages.h>

#define SYMB_COEFF_VAR "symb_coeff#"
#define COMPLEXITY_COUNTER_PREFIX "__CPROVER_CPLX_CNT_"

/*******************************************************************\

Function: predabs_domaint::initialize

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void predabs_domaint::initialize(valuet &value)
{
  templ_valuet &v = static_cast<templ_valuet&>(value);
  v.resize(templ.size());
  for(unsigned row = 0; row<templ.size(); row++)
  {
    v[row] = false_exprt(); //start from top (we can only use a gfp solver for this domain)
  }
}

/*******************************************************************\

Function: predabs_domaint::get_row_pre_constraint

  Inputs:

 Outputs:

 Purpose: pre_guard ==> (row_value => row_expr) 

\*******************************************************************/

exprt predabs_domaint::get_row_constraint(const rowt &row, 
  const row_valuet &row_value)
{
  assert(row<templ.size());
  kindt k = templ[row].kind;
  if(k==OUT || k==OUTL) return true_exprt();
  return implies_exprt(row_value,templ[row].expr);
}

exprt predabs_domaint::get_row_pre_constraint(const rowt &row, 
  const row_valuet &row_value)
{
  assert(row<templ.size());
  const template_rowt &templ_row = templ[row];
  kindt k = templ_row.kind;
  if(k==OUT || k==OUTL) return true_exprt();
  return implies_exprt(row_value,templ[row].expr);
}


exprt predabs_domaint::get_row_pre_constraint(const rowt &row, 
  const templ_valuet &value)
{
  assert(value.size()==templ.size());
  return get_row_pre_constraint(row,value[row]);
}

/*******************************************************************\

Function: predabs_domaint::get_row_post_constraint

  Inputs:

 Outputs:

 Purpose: post_guard => (row_value => row_expr) 

\*******************************************************************/

exprt predabs_domaint::get_row_post_constraint(const rowt &row, 
  const row_valuet &row_value)
{
  assert(row<templ.size());
  const template_rowt &templ_row = templ[row];
  if(templ_row.kind==IN) return true_exprt();
  exprt c = implies_exprt(templ_row.post_guard, 
    implies_exprt(row_value,templ[row].expr));
  if(templ_row.kind==LOOP) rename(c);
  return c;
}

exprt predabs_domaint::get_row_post_constraint(const rowt &row, 
  const templ_valuet &value)
{
  assert(value.size()==templ.size());
  return get_row_post_constraint(row,value[row]);
}

/*******************************************************************\

Function: predabs_domaint::to_pre_constraints

  Inputs:

 Outputs:

 Purpose: /\_all_rows ( pre_guard ==> (row_value => row_expr) ) 

\*******************************************************************/

exprt predabs_domaint::to_pre_constraints(const templ_valuet &value)
{
  assert(value.size()==templ.size());
  exprt::operandst c; 
  for(unsigned row = 0; row<templ.size(); row++)
  {
    c.push_back(get_row_pre_constraint(row,value[row]));
  }
  return conjunction(c); 
}

/*******************************************************************\

Function: predabs_domaint::make_not_post_constraints

  Inputs:

 Outputs:

 Purpose: for all rows !(post_guard ==> (row_value => row_expr) )
          to be connected disjunctively

\*******************************************************************/

void predabs_domaint::make_not_post_constraints(const templ_valuet &value,
  exprt::operandst &cond_exprs)
{
  assert(value.size()==templ.size());
  cond_exprs.resize(templ.size());

  exprt::operandst c; 
  for(unsigned row = 0; row<templ.size(); row++)
  {
    cond_exprs[row] = and_exprt(templ[row].aux_expr,
				not_exprt(get_row_post_constraint(row,value)));
  }
}

/*******************************************************************\

Function: predabs_domaint::get_row_value

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

predabs_domaint::row_valuet predabs_domaint::get_row_value(
  const rowt &row, const templ_valuet &value)
{
  assert(row<value.size());
  assert(value.size()==templ.size());
  return value[row];
}

/*******************************************************************\

Function: predabs_domaint::project_on_vars

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void predabs_domaint::project_on_vars(valuet &value, 
				       const var_sett &vars, exprt &result)
{
  const templ_valuet &v = static_cast<const templ_valuet &>(value);

  assert(v.size()==templ.size());
  exprt::operandst c;
  for(unsigned row = 0; row<templ.size(); row++)
  {
    const template_rowt &templ_row = templ[row];

    std::set<symbol_exprt> symbols;
    find_symbols(templ_row.expr,symbols);

    bool pure = true;
    for(std::set<symbol_exprt>::iterator it = symbols.begin();
	it != symbols.end(); it++)
    {
      if(vars.find(*it)==vars.end()) 
      {
        pure = false;
        break;
      }
    }
    if(!pure) continue;

    const row_valuet &row_v = v[row];
    if(templ_row.kind==LOOP)
    {
      c.push_back(implies_exprt(templ_row.pre_guard,
				implies_exprt(row_v,templ_row.expr)));
    }
    else
    {
      c.push_back(implies_exprt(row_v,templ_row.expr));
    }
  }
  result = conjunction(c);
}

/*******************************************************************\

Function: predabs_domaint::set_row_value

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void predabs_domaint::set_row_value(
  const rowt &row, const predabs_domaint::row_valuet &row_value, templ_valuet &value)
{
  assert(row<value.size());
  assert(value.size()==templ.size());
  value[row] = row_value;
}

/*******************************************************************\

Function: predabs_domaint::output_value

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void predabs_domaint::output_value(std::ostream &out, const valuet &value, 
  const namespacet &ns) const
{
  const templ_valuet &v = static_cast<const templ_valuet &>(value);
  for(unsigned row = 0; row<templ.size(); row++)
  {
    const template_rowt &templ_row = templ[row];
    switch(templ_row.kind)
    {
    case LOOP:
      out << "(LOOP) [ " << from_expr(ns,"",templ_row.pre_guard) << " | ";
      out << from_expr(ns,"",templ_row.post_guard) << " | ";
      out << from_expr(ns,"",templ_row.aux_expr) << " ] ===> " << std::endl << "       ";
      break;
    case IN: out << "(IN)   "; break;
    case OUT: case OUTL: out << "(OUT)  "; break;
    default: assert(false);
    }
    out << "( " << from_expr(ns,"",v[row]) << " ==> " <<
       from_expr(ns,"",templ_row.expr) << " )" << std::endl;
  }
}

/*******************************************************************\

Function: predabs_domaint::output_domain

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void predabs_domaint::output_domain(std::ostream &out, const namespacet &ns) const
{
  for(unsigned row = 0; row<templ.size(); row++)
  {
    const template_rowt &templ_row = templ[row];
    switch(templ_row.kind)
    {
    case LOOP:
      out << "(LOOP) [ " << from_expr(ns,"",templ_row.pre_guard) << " | ";
      out << from_expr(ns,"",templ_row.post_guard) << " | ";
      out << from_expr(ns,"",templ_row.aux_expr) << " ] ===> " << std::endl << "      ";
      break;
    case IN: 
      out << "(IN)   ";
      out << from_expr(ns,"",templ_row.pre_guard) << " ===> " << std::endl << "      ";
      break;
    case OUT: case OUTL:
      out << "(OUT)  "; 
      out << from_expr(ns,"",templ_row.post_guard) << " ===> " << std::endl << "      ";
      break;
    default: assert(false);
    }
    out << "( " << 
        from_expr(ns,"",templ_row.expr) << ")" << std::endl;
  }
}

/*******************************************************************\

Function: predabs_domaint::template_size

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

unsigned predabs_domaint::template_size()
{
  return templ.size();
}

/*******************************************************************\

Function: add_template_row

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

predabs_domaint::template_rowt &predabs_domaint::add_template_row(
  const exprt& expr,
  const exprt& pre_guard,
  const exprt& post_guard,
  const exprt& aux_expr,
  kindt kind
  )
{
  templ.push_back(template_rowt());
  template_rowt &templ_row = templ.back();
  templ_row.expr = expr;
  //extend_expr_types(templ_row.expr);
  templ_row.pre_guard = pre_guard;
  templ_row.post_guard = post_guard;
  templ_row.aux_expr = aux_expr;
  templ_row.kind = kind;
  return templ_row;
}

/*******************************************************************\

Function: equality_domaint::get_var_pairs

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void predabs_domaint::get_row_set(std::set<rowt> &rows) 
{
  for(unsigned i=0;i<templ.size(); i++) rows.insert(i);
}
