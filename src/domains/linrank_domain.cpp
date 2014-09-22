#include "linrank_domain.h"
#include "template_domain.h"

#include <iostream>

#include <util/find_symbols.h>
#include <util/i2string.h>
#include <util/simplify_expr.h>
#include <langapi/languages.h>

#define SYMB_BOUND_VAR "symb_coeff#"

#define EXTEND_TYPES

void linrank_domaint::initialize(valuet &value)
{
	templ_valuet &v = static_cast<templ_valuet&>(value);
	v.resize(templ.size());
	for(unsigned row = 0; row<templ.size(); row++)
		v[row].d = false_exprt();
}

exprt linrank_domaint::get_not_constraints(const linrank_domaint::templ_valuet &value,
			    exprt::operandst &cond_exprs,
			std::vector<linrank_domaint::pre_post_valuest> &value_exprs)
{
  cond_exprs.resize(value.size());
  value_exprs.resize(value.size());

  for(unsigned row = 0; row<templ.size(); row++)
  {
    value_exprs[row].insert(value_exprs[row].end(),templ[row].expr.begin(),templ[row].expr.end()); 

    if(is_row_value_true(value[row]))
    {
      // !(g => true)
      cond_exprs[row] = false_exprt();
    }
    else if(is_row_value_false(value[row]))
    {
      // !(g => false)
      cond_exprs[row] = 
	and_exprt(templ[row].pre_guard, templ[row].post_guard); 
    }
    else
    {
      std::cout << "value.c.size: " << value[row].c.size() << std::endl;
      std::cout << "temp.expr.size: " << templ[row].expr.size() << std::endl;

      assert(value[row].c.size()==templ[row].expr.size());

      exprt sum_first = value[row].d;
      exprt sum_second = value[row].d;
      for(unsigned i = 0; i < value[row].c.size(); ++i)
      {
        sum_first = plus_exprt(sum_first, mult_exprt(value[row].c[i], templ[row].expr[i].first));
        sum_second = plus_exprt(sum_second, mult_exprt(value[row].c[i], templ[row].expr[i].second));
      }
      //extend types
#ifdef EXTEND_TYPES
      extend_expr_types(sum_first);
      extend_expr_types(sum_second);
#endif

      exprt bounded = binary_relation_exprt(sum_first, ID_gt, from_integer(mp_integer(0),sum_first.type()));
      exprt decreasing = binary_relation_exprt(sum_first, ID_gt, sum_second);

      cond_exprs[row] = not_exprt(implies_exprt(and_exprt(templ[row].pre_guard, templ[row].post_guard),
						and_exprt(bounded, decreasing)));
    }
  }

  return disjunction(cond_exprs);
}

exprt linrank_domaint::get_row_symb_constraint(linrank_domaint::row_valuet &symb_values, // contains vars c and d
					      const linrank_domaint::rowt &row,
					      linrank_domaint::pre_post_valuest &values)
{
  symb_values.c.resize(values.size());

  symb_values.d = symbol_exprt(SYMB_BOUND_VAR+std::string("d!")+i2string(row), 
			       signedbv_typet(32)); //coefficients are 32bit signed integers
  exprt sum_first = symb_values.d;
  exprt sum_second = symb_values.d;
  for(unsigned i = 0; i < values.size(); ++i)
  {
    symb_values.c[i] = symbol_exprt(SYMB_BOUND_VAR+std::string("c!")+i2string(row)+"$"+i2string(i), 
				    signedbv_typet(32));  //coefficients are 32bit signed integers
    sum_first = plus_exprt(sum_first, mult_exprt(symb_values.c[i], values[i].first));
    sum_second = plus_exprt(sum_second, mult_exprt(symb_values.c[i], values[i].second));
  }
  //extend types
#ifdef EXTEND_TYPES
  extend_expr_types(sum_first);
  extend_expr_types(sum_second);
#endif

  exprt bounded = binary_relation_exprt(sum_first, ID_gt, 
       from_integer(mp_integer(0),sum_first.type()));
  exprt decreasing = binary_relation_exprt(sum_first, ID_gt, sum_second);

  return and_exprt(bounded, decreasing);
}

linrank_domaint::row_valuet linrank_domaint::get_row_value(const rowt &row, const templ_valuet &value)
{
	assert(row<value.size());
	assert(value.size()==templ.size());
	return value[row];
}

void linrank_domaint::set_row_value(const rowt &row, const row_valuet &row_value, templ_valuet &value)
{
	assert(row<value.size());
	assert(value.size()==templ.size());
	value[row] = row_value;
}

void linrank_domaint::set_row_value_to_true(const rowt &row, templ_valuet &value)
{
	assert(row<value.size());
	assert(value.size()==templ.size());
	value[row].d = true_exprt();
}

void linrank_domaint::output_value(std::ostream &out, const valuet &value,
  const namespacet &ns) const
{
  const templ_valuet &v = static_cast<const templ_valuet &>(value);
  for(unsigned row = 0; row<templ.size(); row++)
  {
    const template_rowt &templ_row = templ[row];
    switch(templ_row.kind)
    {
    case LOOP:
      out << "(RANK) [ " << from_expr(ns,"",templ_row.pre_guard) << " | ";
      out << from_expr(ns,"",templ_row.post_guard) << " ] ===> " << std::endl << "       ";
      break;
    default: assert(false);
    }

    for(unsigned i = 0; i<templ_row.expr.size(); ++i)
    {
      out << from_expr(ns,"",v[row].c[i]) << " * "
	  << from_expr(ns,"",templ_row.expr[i].first) << " + ";
    }
    out << from_expr(ns,"",v[row].d) << std::endl;
  }
}

void linrank_domaint::output_domain(std::ostream &out, const namespacet &ns) const
{
  for(unsigned row = 0; row<templ.size(); row++)
  {
    const template_rowt &templ_row = templ[row];
    switch(templ_row.kind)
    {
    case LOOP:
      out << "(RANK) (" << from_expr(ns,"",templ_row.pre_guard) << ") && ("
          << from_expr(ns,"",templ_row.post_guard) << ") ===> " 
          << std::endl << "      ";
      break;
    default: assert(false);
    }

    for(unsigned i = 0; i<templ_row.expr.size(); ++i)
    {
      out << "c!" << row << "$" << i << " * "
	  << from_expr(ns,"",templ_row.expr[i].first) << " + ";
    }
    out << "d!" << row << std::endl;
  }
}

void linrank_domaint::project_on_loops(const valuet &value, exprt &result)
{
  const templ_valuet &v = static_cast<const templ_valuet &>(value);
  assert(v.size()==templ.size());
  exprt::operandst c;
  c.reserve(templ.size());
  for(unsigned row = 0; row<templ.size(); row++)
  {
    assert(templ[row].kind == LOOP);

    if(is_row_value_false(v[row]))
    {
      //(g => false)
      c.push_back(implies_exprt(
		    and_exprt(templ[row].pre_guard, templ[row].post_guard),
		    false_exprt()));
    }
    else if(is_row_value_true(v[row]))
    {
      //(g => true)
      c.push_back(implies_exprt(
		    and_exprt(templ[row].pre_guard, templ[row].post_guard),
		    true_exprt()));
    }
    else
    {
      exprt sum_first = v[row].d;
      exprt sum_second = v[row].d;
      for(unsigned i = 0; i < v[row].c.size(); ++i)
      {
	sum_first = plus_exprt(sum_first, mult_exprt(v[row].c[i], 
						     templ[row].expr[i].first));
	sum_second = plus_exprt(sum_second, mult_exprt(v[row].c[i], 
						       templ[row].expr[i].second));
      }
      //extend types
#ifdef EXTEND_TYPES
      extend_expr_types(sum_first);
      extend_expr_types(sum_second);
#endif
      exprt bounded = binary_relation_exprt(sum_first, ID_gt, 
					    from_integer(mp_integer(0), sum_first.type()));
      exprt decreasing = binary_relation_exprt(sum_first, ID_gt, sum_second);

      c.push_back(implies_exprt(and_exprt(templ[row].pre_guard, templ[row].post_guard),
				and_exprt(bounded, decreasing)));
    }
  }
  result = conjunction(c);
}

void linrank_domaint::project_on_out(const valuet &value, exprt &result)
{
  result = true_exprt();
}

void linrank_domaint::project_on_inout(const valuet &value, exprt &result)
{
  result = true_exprt();
}

void linrank_domaint::project_on_vars(const valuet &value, const var_sett &vars, exprt &result)
{
#if 0
	const templ_valuet &v = static_cast<const templ_valuet &>(value);
	assert(v.size()==templ.size());
	exprt::operandst c;
	for(unsigned row = 0; row<templ.size(); row++)
	{
		const template_rowt &templ_row = templ[row];

    //FIXME:
		std::set<symbol_exprt> symbols;
    for(unsigned i=0; i<templ_row.expr.size(); ++i)
      find_symbols(templ_row.expr[i].first,symbols);

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

    //FIXME:
    for(unsigned i=0; i<templ_row.expr.size(); ++i)
      c.push_back(binary_relation_exprt(templ_row.expr[i].first,ID_le,v[row].c[i]));
	}
	result = conjunction(c);
#endif
result = true_exprt();
}

/*******************************************************************\

Function: linrank_domaint::add_template

  Inputs:

 Outputs:

 Purpose: This is called for each loop.

\*******************************************************************/

void linrank_domaint::add_template(const var_specst &var_specs,
				   const namespacet &ns)
{
  bool has_loop = false;
  for(var_specst::const_iterator v = var_specs.begin();
      v!=var_specs.end(); v++)
  {
    if(v->kind==LOOP)
    {
      has_loop = true;
      break;
    }
  }
  if(!has_loop) return;

  templ.reserve(templ.size()+1);
  templ.push_back(template_rowt());
  template_rowt &templ_row = templ.back();
  templ_row.kind = LOOP;

  exprt::operandst preg;
  exprt::operandst postg;

  for(var_specst::const_iterator v = var_specs.begin();
      v!=var_specs.end(); v++)
  {
    if(v->kind!=LOOP) continue;
    preg.push_back(v->pre_guard);
    postg.push_back(v->post_guard);
    exprt vpost = v->var; //copy
    rename(vpost);
    templ_row.expr.push_back(std::pair<exprt,exprt>(v->var,vpost));
  }

  templ_row.pre_guard = conjunction(preg);
  templ_row.post_guard = conjunction(postg);
}

/*******************************************************************\

Function: linrank_domaint::is_row_value_false

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool linrank_domaint::is_row_value_false(const row_valuet & row_value) const
{
  return row_value.d.get(ID_value)==ID_false;
}

/*******************************************************************\

Function: linrank_domaint::is_row_value_true

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool linrank_domaint::is_row_value_true(const row_valuet & row_value) const
{
  return row_value.d.get(ID_value)==ID_true;
}
