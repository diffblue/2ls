#include "lexlinrank_domain.h"
#include "tpolyhedra_domain.h"

#include <iostream>

#include <util/find_symbols.h>
#include <util/i2string.h>
#include <util/simplify_expr.h>
#include <langapi/languages.h>

#define SYMB_BOUND_VAR "symb_coeff#"

#define EXTEND_TYPES

#define COEFF_C_SIZE 2
#define COEFF_D_SIZE 10

void lexlinrank_domaint::initialize(valuet &value)
{
  templ_valuet &v = static_cast<templ_valuet&>(value);
  v.resize(templ.size());
  for(unsigned row = 0; row<templ.size(); row++)
  {
    v[row].resize(1);
    v[row][0].d = false_exprt();
    v[row][0].c.clear();
  }
}

exprt lexlinrank_domaint::get_not_constraints(const lexlinrank_domaint::templ_valuet &value,
			    exprt::operandst &cond_exprs,
			std::vector<lexlinrank_domaint::pre_post_valuest> &value_exprs)
{
  cond_exprs.resize(value.size());
  value_exprs.resize(value.size());

  for(unsigned row = 0; row<templ.size(); row++)
  {
    value_exprs[row].insert(value_exprs[row].end(),templ[row].expr.begin(),templ[row].expr.end()); 

    std::cout << "temp.expr.size: " << templ[row].expr.size() << std::endl;

    exprt::operandst elmts;
    elmts.reserve(value[row].size());
    for(unsigned elm=0; elm<value[row].size(); ++elm)
    {
      if(is_row_element_value_true(value[row][elm]))
      {
	// !(g => true)
	cond_exprs[row] = false_exprt();
      }
      else if(is_row_element_value_false(value[row][elm]))
      {
	// !(g => false)
	cond_exprs[row] = 
          and_exprt(templ[row].pre_guard, templ[row].post_guard);
      }
      else
      {
        std::cout << "value[" << elm << "].c.size: " << value[row][elm].c.size() << std::endl;

        assert(value[row][elm].c.size()==templ[row].expr.size());

        exprt::operandst c;
        c.reserve(2 + value[row].size() - (elm+1));

        exprt sum_first = value[row][elm].d;
        exprt sum_second = value[row][elm].d;
        for(unsigned i = 0; i < value[row][elm].c.size(); ++i)
        {
          sum_first = plus_exprt(sum_first, mult_exprt(value[row][elm].c[i], templ[row].expr[i].first));
          sum_second = plus_exprt(sum_second, mult_exprt(value[row][elm].c[i], templ[row].expr[i].second));
        }
        //extend types
#ifdef EXTEND_TYPES
        extend_expr_types(sum_first);
        extend_expr_types(sum_second);
#endif

        // bounded
        c.push_back( binary_relation_exprt(sum_first, ID_gt, from_integer(mp_integer(0),sum_first.type())) );
        // decreasing
        c.push_back( binary_relation_exprt(sum_first, ID_gt, sum_second) );

        for(unsigned elm2=elm+1; elm2<value[row].size(); ++elm2)
        {
          // excluding d from the sums as it cancels itself
          exprt sum_first2 = from_integer(mp_integer(0), value[row][elm2].d.type());
          exprt sum_second2 = from_integer(mp_integer(0), value[row][elm2].d.type());
          for(unsigned i = 0; i < value[row][elm2].c.size(); ++i)
          {
            sum_first2 = plus_exprt(sum_first2, mult_exprt(value[row][elm2].c[i], templ[row].expr[i].first));
            sum_second2 = plus_exprt(sum_second2, mult_exprt(value[row][elm2].c[i], templ[row].expr[i].second));
          }
          //extend types
#ifdef EXTEND_TYPES
          extend_expr_types(sum_first2);
          extend_expr_types(sum_second2);
#endif

          // non-increasing
          c.push_back( binary_relation_exprt(sum_first2, ID_ge, sum_second2) );
        }

        elmts.push_back(conjunction(c));
      }

      cond_exprs[row] =
        not_exprt(
          implies_exprt(
              and_exprt(templ[row].pre_guard, templ[row].post_guard),
              disjunction(elmts)));
    }
  }

  return disjunction(cond_exprs);
}

exprt lexlinrank_domaint::get_row_symb_constraint(lexlinrank_domaint::row_valuet &symb_values, // contains vars c and d
					      const lexlinrank_domaint::rowt &row,
					      lexlinrank_domaint::pre_post_valuest &values)
{
  // NOTE: I assume symb_values.size was set to the number of
  // desired elements in the lexicographic before calling this function

  exprt::operandst d;
  d.reserve(symb_values.size());

  // we iterate in reverse as we init symbols the inner iteration uses
  for(int elm=symb_values.size()-1; elm>=0; --elm)
  {
    symb_values[elm].c.resize(values.size());

    symb_values[elm].d = 
      symbol_exprt(SYMB_BOUND_VAR+std::string("d!")+i2string(row)+std::string("$")+i2string(elm),
		   signedbv_typet(COEFF_D_SIZE));

    exprt::operandst c;
    c.reserve(2 + symb_values.size() - (elm+1));

    exprt sum_first = symb_values[elm].d;
    exprt sum_second = symb_values[elm].d;
    for(unsigned i = 0; i < values.size(); ++i)
    {
      symb_values[elm].c[i] = 
       symbol_exprt(SYMB_BOUND_VAR+std::string("c!")+i2string(row)+"$"+i2string(elm)+"$"+i2string(i),
		     signedbv_typet(COEFF_C_SIZE));
      sum_first = plus_exprt(sum_first, mult_exprt(symb_values[elm].c[i], values[i].first));
      sum_second = plus_exprt(sum_second, mult_exprt(symb_values[elm].c[i], values[i].second));
    }
    //extend types
#ifdef EXTEND_TYPES
    extend_expr_types(sum_first);
    extend_expr_types(sum_second);
#endif

    // bounded
    c.push_back( binary_relation_exprt(sum_first, ID_gt,
         from_integer(mp_integer(0),sum_first.type())) );
    // decreasing
    c.push_back( binary_relation_exprt(sum_first, ID_gt, sum_second) );

    for(unsigned elm2=elm+1; elm2<symb_values.size(); ++elm2)
    {
      // excluding d from the sums as it cancels itself
      exprt sum_first2 = from_integer(mp_integer(0), symb_values[elm2].d.type());
      exprt sum_second2 = from_integer(mp_integer(0), symb_values[elm2].d.type());
      for(unsigned i = 0; i < values.size(); ++i)
      {
        sum_first2 = plus_exprt(sum_first2, mult_exprt(symb_values[elm2].c[i], values[i].first));
        sum_second2 = plus_exprt(sum_second2, mult_exprt(symb_values[elm2].c[i], values[i].second));
      }
      //extend types
#ifdef EXTEND_TYPES
      extend_expr_types(sum_first2);
      extend_expr_types(sum_second2);
#endif
      // non-increasing
      c.push_back( binary_relation_exprt(sum_first2, ID_ge, sum_second2) );
    }

    d.push_back(conjunction(c));
  }

  return disjunction(d);
}

lexlinrank_domaint::row_valuet lexlinrank_domaint::get_row_value(const rowt &row, const templ_valuet &value)
{
	assert(row<value.size());
	assert(value.size()==templ.size());
	return value[row];
}

void lexlinrank_domaint::set_row_value(const rowt &row, const row_valuet &row_value, templ_valuet &value)
{
	assert(row<value.size());
	assert(value.size()==templ.size());
	value[row] = row_value;
}

void lexlinrank_domaint::set_row_value_to_true(const rowt &row, templ_valuet &value)
{
	assert(row<value.size());
	assert(value.size()==templ.size());
	value[row].resize(1);
	value[row][0].d = true_exprt();
}

void lexlinrank_domaint::output_value(std::ostream &out, const valuet &value,
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
      out << from_expr(ns,"",templ_row.post_guard) << " ] ===> " << std::endl;
      break;
    default: assert(false);
    }

    for(unsigned elm=0; elm<v[row].size(); ++elm)
    {
      out << "       ";
      for(unsigned i = 0; i<templ_row.expr.size(); ++i)
      {
        out << from_expr(ns,"",v[row][elm].c[i]) << " * "
            << from_expr(ns,"",templ_row.expr[i].first) << " + ";
      }
      out << from_expr(ns,"",v[row][elm].d) << std::endl;
    }
  }
}

void lexlinrank_domaint::output_domain(std::ostream &out, const namespacet &ns) const
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

void lexlinrank_domaint::project_on_vars(valuet &value, const var_sett &vars, exprt &result)
{
//TODO: fix this
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

  const templ_valuet &v = static_cast<const templ_valuet &>(value);
  assert(v.size()==templ.size());
  exprt::operandst c;
  c.reserve(templ.size());
  for(unsigned row = 0; row<templ.size(); row++)
  {
    assert(templ[row].kind == LOOP);

    exprt::operandst elmnts;
    elmnts.reserve(v[row].size());
    for(unsigned elm=0; elm<v[row].size(); ++elm)
    {
      if(is_row_element_value_false(v[row][elm]))
      {
	//(g => false)
	c.push_back(implies_exprt(
		      and_exprt(templ[row].pre_guard, templ[row].post_guard),
		      false_exprt()));
      }
      else if(is_row_element_value_true(v[row][elm]))
      {
	//(g => true)
	c.push_back(implies_exprt(
		      and_exprt(templ[row].pre_guard, templ[row].post_guard),
		      true_exprt()));
      }
      else
      {
	exprt::operandst con;
	con.reserve(2 + v[row].size() - (elm+1));

	exprt sum_first = v[row][elm].d;
	exprt sum_second = v[row][elm].d;
	for(unsigned i = 0; i < v[row][elm].c.size(); ++i)
	{
	  sum_first = plus_exprt(sum_first, mult_exprt(v[row][elm].c[i],
						       templ[row].expr[i].first));
	  sum_second = plus_exprt(sum_second, mult_exprt(v[row][elm].c[i],
							 templ[row].expr[i].second));
	}
	//extend types
#ifdef EXTEND_TYPES
	extend_expr_types(sum_first);
	extend_expr_types(sum_second);
#endif
	// bounded
	con.push_back( binary_relation_exprt(sum_first, ID_gt,
					     from_integer(mp_integer(0), sum_first.type())) );
	// decreasing
	con.push_back( binary_relation_exprt(sum_first, ID_gt, sum_second) );

	for(unsigned elm2=elm+1; elm2<v[row].size(); ++elm2)
	{
	  // excluding d from the sums as it cancels itself
	  exprt sum_first2 = from_integer(mp_integer(0), v[row][elm2].d.type());
	  exprt sum_second2 = from_integer(mp_integer(0), v[row][elm2].d.type());
	  for(unsigned i = 0; i < v[row][elm2].c.size(); ++i)
	  {
	    sum_first2 = plus_exprt(sum_first2, mult_exprt(v[row][elm2].c[i],
							   templ[row].expr[i].first));
	    sum_second2 = plus_exprt(sum_second2, mult_exprt(v[row][elm2].c[i],
							     templ[row].expr[i].second));
	  }
	  //extend types
#ifdef EXTEND_TYPES
	  extend_expr_types(sum_first2);
	  extend_expr_types(sum_second2);
#endif
	  // non-increasing
	  con.push_back( binary_relation_exprt(sum_first2, ID_ge, sum_second2) );
	}

	elmnts.push_back(
	  implies_exprt(
	    and_exprt(templ[row].pre_guard, templ[row].post_guard),
	    conjunction(con)) );
      }

      c.push_back(disjunction(elmnts));
    }
  }
  result = conjunction(c);
}

/*******************************************************************\

Function: lexlinrank_domaint::add_template

  Inputs:

 Outputs:

 Purpose: This is called for each loop.

\*******************************************************************/

void lexlinrank_domaint::add_template(const var_specst &var_specs,
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

Function: lexlinrank_domaint::is_row_value_false

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool lexlinrank_domaint::is_row_value_false(const row_valuet & row_value) const
{
  assert(false);
  //return row_value.size() >= 1 && row_value[0].d.get(ID_value) == ID_false;
}

bool lexlinrank_domaint::is_row_element_value_false(const row_value_elementt & row_value_element) const
{
  return row_value_element.d.get(ID_value) == ID_false;
}

/*******************************************************************\

Function: lexlinrank_domaint::is_row_value_true

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool lexlinrank_domaint::is_row_value_true(const row_valuet & row_value) const
{
  assert(false);
  // return row_value.size() == 1 && row_value[0].d.get(ID_value) == ID_true;
}

bool lexlinrank_domaint::is_row_element_value_true(const row_value_elementt & row_value_element) const
{
  return row_value_element.d.get(ID_value) == ID_true;
}

/*******************************************************************\

Function: lexlinrank_domaint::add_element

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void lexlinrank_domaint::add_element(const rowt &row, templ_valuet &value)
{ 
  value[row].push_back(row_value_elementt());
  for(unsigned i=0; i<value[row].size(); i++)
  {
    value[row][i].c.clear();
    value[row][i].d = false_exprt();
  }
}
