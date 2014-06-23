#include "equality_domain.h"

#include <iostream>

#include <util/find_symbols.h>
#include <util/arith_tools.h>
#include <util/ieee_float.h>
#include <util/simplify_expr.h>
#include <langapi/languages.h>

/*******************************************************************\

Function: equality_domaint::initialize

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void equality_domaint::initialize(valuet &value)
{
  /*  value.resize(templ.size());
  for(unsigned index = 0; index<templ.size(); index++)
  {
    if(templ.kinds[index]==IN) value[index] = true_exprt(); //marker for oo
    else value[index] = false_exprt(); //marker for -oo
    }*/
}

exprt equality_domaint::get_pre_equ_constraint(const var_pairt &vv)
{
  return equal_exprt(vv.first,vv.second);
}

exprt equality_domaint::get_post_not_equ_constraint(const var_pairt &vv)
{
  return notequal_exprt(vv.first,vv.second);
}

exprt equality_domaint::get_pre_disequ_constraint(const var_pairt &vv)
{
  return notequal_exprt(vv.first,vv.second);
}

exprt equality_domaint::get_post_not_disequ_constraint(const var_pairt &vv)
{
  return equal_exprt(vv.first,vv.second);
}



/*******************************************************************\

Function: equality_domaint::project_on_loops

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void equality_domaint::project_on_loops(const valuet &value, exprt &result)
{
  //  assert(value.size()==templ.size());
  exprt::operandst c;
  /* c.reserve(templ.size());
  for(unsigned row = 0; row<templ.size(); row++)
  {
    if(templ.kinds[row]!=LOOP) continue;
    const row_valuet &row_value = value[row];
    if(is_row_value_neginf(row_value)) c.push_back(false_exprt());
    else if(is_row_value_inf(row_value)) c.push_back(true_exprt());
    else c.push_back(binary_relation_exprt(templ.rows[row],ID_le,row_value));
  }*/
  result = true_exprt(); //conjunction(c);
}

/*******************************************************************\

Function: equality_domaint::project_on_inout

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void equality_domaint::project_on_inout(const valuet &value, exprt &result)
{
  //  assert(value.size()==templ.size());
  exprt::operandst c;
  /*  c.reserve(templ.size());
  for(unsigned row = 0; row<templ.size(); row++)
  {
    kindt k = templ.kinds[row];
    if(k==LOOP || k==OUTL) continue;
    const row_valuet &row_value = value[row];
    if(is_row_value_neginf(row_value)) c.push_back(false_exprt());
    else if(is_row_value_inf(row_value)) c.push_back(true_exprt());
    else c.push_back(binary_relation_exprt(templ.rows[row],ID_le,row_value));
    }*/
  result = true_exprt(); //conjunction(c); 
}

/*******************************************************************\

Function: equality_domaint::set_equal

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void equality_domaint::set_equal(
  const var_pairt &vv, equ_valuet &value)
{
  value.equs.make_union(vv.first,vv.second);
}

/*******************************************************************\

Function: equality_domaint::set_unequal

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void equality_domaint::set_disequal(
  const var_pairt &vv, equ_valuet &value)
{
  value.disequs.insert(vv);
}

/*******************************************************************\

Function: equality_domaint::output_value

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void equality_domaint::output_value(std::ostream &out, const valuet &value, 
  const namespacet &ns) const
{
  /*  for(unsigned row = 0; row<templ.size(); row++)
  {
    switch(templ.kinds[row])
    {
    case LOOP:
      out << "(LOOP) [ " << from_expr(ns,"",templ.pre_guards[row]) << " | ";
      out << from_expr(ns,"",templ.post_guards[row]) << " ] ===> " << std::endl << "       ";
      break;
    case IN: out << "(IN)   "; break;
    case OUT: case OUTL: out << "(OUT)  "; break;
    default: assert(false);
    }
    out << "( " << from_expr(ns,"",templ.rows[row]) << " <= ";
    if(is_row_value_neginf(value[row])) out << "-oo";
    else if(is_row_value_inf(value[row])) out << "oo";
    else out << from_expr(ns,"",value[row]);
    out << " )" << std::endl;
    }*/
}

/*******************************************************************\

Function: equality_domaint::output_domain

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void equality_domaint::output_domain(std::ostream &out, 
  const namespacet &ns) const
{
  for(unsigned index = 0; index<vars.size(); index++)
  {
    switch(kinds[index])
    {
    case LOOP:
      out << "(LOOP) ";
	//[ " << from_expr(ns,"",templ.pre_guards[row]) << " | ";
	//      out << from_expr(ns,"",templ.post_guards[row]) << " ] ===> " << std::endl << "      ";
      break;
    case IN: out << "(IN)   "; break;
    case OUT: case OUTL:
      out << "(OUT)  "; 
      //      out << from_expr(ns,"",templ.post_guards[row]) << " ===> " << std::endl << "      ";
      break;
    default: assert(false);
    }
    out << from_expr(ns,"",vars[index]) << std::endl;
  }
}
