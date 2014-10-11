#include "linrank_domain.h"
#include "util.h"

#include <iostream>

#include <util/find_symbols.h>
#include <util/i2string.h>
#include <util/simplify_expr.h>
#include <langapi/languages.h>

#define SYMB_COEFF_VAR "symb_coeff#"

#define EXTEND_TYPES
#define DIFFERENCE_ENCODING

#define COEFF_C_SIZE 10
#define MAX_REFINEMENT 2

void linrank_domaint::initialize(valuet &value)
{
  templ_valuet &v = static_cast<templ_valuet&>(value);
  v.resize(templ.size());
  for(unsigned row = 0; row<templ.size(); row++)
  {
    v[row].c.resize(1);
    v[row].c[0] = false_exprt();
  }
}

bool linrank_domaint::refine()
{ 
  if(refinement_level>=MAX_REFINEMENT) return false;
  refinement_level++; 
  return true;
}

exprt linrank_domaint::get_not_constraints(
  const linrank_domaint::templ_valuet &value,
  exprt::operandst &cond_exprs,
  std::vector<linrank_domaint::pre_post_valuest> &value_exprs)
{
  assert(value.size()==templ.size());
  cond_exprs.resize(value.size());
  value_exprs.resize(value.size());

  for(unsigned row = 0; row<templ.size(); row++)
  {
    value_exprs[row].insert(value_exprs[row].end(),
			    templ[row].expr.begin(),templ[row].expr.end()); 

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
      assert(value[row].c.size()==templ[row].expr.size());
      assert(value[row].c.size()>=1);

#ifdef DIFFERENCE_ENCODING
      exprt sum = mult_exprt(value[row].c[0], 
			     minus_exprt(templ[row].expr[0].first,
					 templ[row].expr[0].second));
#else
      exprt sum_pre = mult_exprt(value[row].c[0],templ[row].expr[0].first);
      exprt sum_post = mult_exprt(value[row].c[0],templ[row].expr[0].second);
#endif
      for(unsigned i = 1; i < value[row].c.size(); ++i)
      {
#ifdef DIFFERENCE_ENCODING
        sum = plus_exprt(sum, mult_exprt(value[row].c[i], 
					 minus_exprt(templ[row].expr[i].first,
					 templ[row].expr[i].second)));
#else
	sum_pre = plus_exprt(sum_pre,
			     mult_exprt(value[row].c[i],
					templ[row].expr[i].first));
	sum_post = plus_exprt(sum_post,
			     mult_exprt(value[row].c[i],
					templ[row].expr[i].second));
#endif
      }

#ifdef DIFFERENCE_ENCODING
#ifdef EXTEND_TYPES
      extend_expr_types(sum);
#endif
      exprt decreasing = binary_relation_exprt(sum, ID_gt, 
	from_integer(mp_integer(0),sum.type()));
#else
#ifdef EXTEND_TYPES
      extend_expr_types(sum_pre);
      extend_expr_types(sum_post);
#endif
      exprt decreasing = binary_relation_exprt(sum_pre, ID_gt,sum_post);
#endif
      cond_exprs[row] = not_exprt(implies_exprt(
			  and_exprt(templ[row].pre_guard, 
				    templ[row].post_guard),
                          decreasing));
    }
  }

  return disjunction(cond_exprs);
}

exprt linrank_domaint::get_row_symb_constraint(
  linrank_domaint::row_valuet &symb_values, // contains vars c
  const linrank_domaint::rowt &row,
  const pre_post_valuest &values,
  exprt &refinement_constraint)
{
  symb_values.c.resize(values.size());
  assert(values.size()>=1);
  symb_values.c[0] = symbol_exprt(SYMB_COEFF_VAR+std::string("c!")+
		       i2string(row)+"$0",
    signedbv_typet(COEFF_C_SIZE));  //coefficients are signed integers

#ifdef DIFFERENCE_ENCODING
      exprt sum = mult_exprt(symb_values.c[0], 
			     minus_exprt(values[0].first,
					 values[0].second));
#else
      exprt sum_pre = mult_exprt(symb_values.c[0],values[0].first);
      exprt sum_post = mult_exprt(symb_values.c[0],values[0].second);
#endif
      for(unsigned i = 1; i < symb_values.c.size(); ++i)
      {
	symb_values.c[i] = symbol_exprt(
          SYMB_COEFF_VAR+std::string("c!")+i2string(row)+"$"+i2string(i),
           signedbv_typet(COEFF_C_SIZE));  //coefficients are signed integers
#ifdef DIFFERENCE_ENCODING
        sum = plus_exprt(sum, mult_exprt(symb_values.c[i], 
					 minus_exprt(values[i].first,
					 values[i].second)));
#else
	sum_pre = plus_exprt(sum_pre,
			     mult_exprt(symb_values.c[i],
					values[i].first));
	sum_post = plus_exprt(sum_post,
			     mult_exprt(symb_values.c[i],
					values[i].second));
#endif
      }

  exprt::operandst constraints;
  exprt::operandst ref_constraints;

#ifdef DIFFERENCE_ENCODING
#ifdef EXTEND_TYPES
      extend_expr_types(sum);
#endif
      constant_exprt cst;
      if(sum.type().id()==ID_unsignedbv || sum.type().id()==ID_signedbv)
        cst = from_integer(mp_integer(0),sum.type());
      else if(sum.type().id()==ID_floatbv)
      {
	ieee_floatt zero(to_floatbv_type(sum.type()));
	zero.make_zero();
        cst = zero.to_expr();
      }
      else assert(false);
      exprt decreasing = binary_relation_exprt(sum, ID_gt,cst);
#else
#ifdef EXTEND_TYPES
      extend_expr_types(sum_pre);
      extend_expr_types(sum_post);
#endif
      exprt decreasing = binary_relation_exprt(sum_pre, ID_gt,sum_post);
#endif

  constraints.push_back(decreasing);

#if 1
  //refinement
  if(refinement_level==0)
  {
    for(unsigned i = 0; i < values.size(); ++i)
    {
      typet type = symb_values.c[i].type();
      if(type.id()==ID_signedbv || type.id()==ID_unsignedbv)
      {
	ref_constraints.push_back(
	  binary_relation_exprt(symb_values.c[i],ID_ge,
				from_integer(mp_integer(-1),type)));
	ref_constraints.push_back(
	  binary_relation_exprt(symb_values.c[i],ID_le,
				from_integer(mp_integer(1),type)));
      }
      else if(type.id()==ID_floatbv)
      {
	ieee_floatt zero; zero.make_zero();
	ieee_floatt one; one.from_integer(mp_integer(1));
	ieee_floatt minusone = one; one.negate();
	ref_constraints.push_back(or_exprt(or_exprt(
		     equal_exprt(symb_values.c[i],one.to_expr()),
      		     equal_exprt(symb_values.c[i],zero.to_expr())),
		   equal_exprt(symb_values.c[i],minusone.to_expr())));
      }
    }
  }
  else if(refinement_level==1)
  {
    for(unsigned i = 0; i < values.size(); ++i)
    {
      typet type = symb_values.c[i].type();
      if(type.id()==ID_signedbv || type.id()==ID_unsignedbv)
      {
	ref_constraints.push_back(
	  binary_relation_exprt(symb_values.c[i],ID_ge,
				from_integer(mp_integer(-10),type)));
	ref_constraints.push_back(
	  binary_relation_exprt(symb_values.c[i],ID_le,
				from_integer(mp_integer(10),type)));
      }
    }
  }
#endif

  refinement_constraint = conjunction(ref_constraints);
  return conjunction(constraints);
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
	value[row].c.resize(1);
	value[row].c[0]= true_exprt();
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
      if(i>0) out << " + ";
      out << from_expr(ns,"",v[row].c[i]) << " * "
	  << from_expr(ns,"",templ_row.expr[i].first);
    }
    out << std::endl;
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
      if(i>0) out << " + ";
      out << "c!" << row << "$" << i << " * "
	  << from_expr(ns,"",templ_row.expr[i].first);
    }
    out << std::endl;
  }
}

void linrank_domaint::project_on_vars(valuet &value, const var_sett &vars, exprt &result)
{
  //don't do any projection
  const templ_valuet &v = static_cast<const templ_valuet &>(value);
  assert(v.size()==templ.size());
  exprt::operandst c;
  c.reserve(templ.size());
  for(unsigned row = 0; row<templ.size(); row++)
  {
    assert(templ[row].kind == LOOP);

    if(is_row_value_true(v[row]))
    {
      // (g => true)
      c.push_back(true_exprt());
    }
    else if(is_row_value_false(v[row]))
    {
      // (g => false)
      c.push_back(implies_exprt(and_exprt(templ[row].pre_guard, templ[row].post_guard),false_exprt())); 
    }
    else
    {
      assert(v[row].c.size()==templ[row].expr.size());
      assert(v[row].c.size()>=1);

#ifdef DIFFERENCE_ENCODING
      exprt sum = mult_exprt(v[row].c[0], 
			     minus_exprt(templ[row].expr[0].first,
					 templ[row].expr[0].second));
#else
      exprt sum_pre = mult_exprt(v[row].c[0],templ[row].expr[0].first);
      exprt sum_post = mult_exprt(v[row].c[0],templ[row].expr[0].second);
#endif
      for(unsigned i = 1; i < v[row].c.size(); ++i)
      {
#ifdef DIFFERENCE_ENCODING
        sum = plus_exprt(sum, mult_exprt(v[row].c[i], 
					 minus_exprt(templ[row].expr[i].first,
					 templ[row].expr[i].second)));
#else
	sum_pre = plus_exprt(sum_pre,
			     mult_exprt(v[row].c[i],
					templ[row].expr[i].first));
	sum_post = plus_exprt(sum_post,
			     mult_exprt(v[row].c[i],
					templ[row].expr[i].second));
#endif
      }

#ifdef DIFFERENCE_ENCODING
#ifdef EXTEND_TYPES
      extend_expr_types(sum);
#endif
      exprt decreasing = binary_relation_exprt(sum, ID_gt, 
	from_integer(mp_integer(0),sum.type()));
#else
#ifdef EXTEND_TYPES
      extend_expr_types(sum_pre);
      extend_expr_types(sum_post);
#endif
      exprt decreasing = binary_relation_exprt(sum_pre, ID_gt,sum_post);
#endif
      c.push_back(implies_exprt(
		    and_exprt(templ[row].pre_guard, 
			      templ[row].post_guard),
                          decreasing));
    }
  }
  result = conjunction(c);
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
  assert(row_value.c.size()>=1);
  return row_value.c[0].get(ID_value)==ID_false;
}

/*******************************************************************\

Function: linrank_domaint::is_row_value_true

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool linrank_domaint::is_row_value_true(const row_valuet & row_value) const
{
  assert(row_value.c.size()>=1);
  return row_value.c[0].get(ID_value)==ID_true;
}
