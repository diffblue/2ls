#include "linrank_domain.h"
#include "template_domain.h"

#include <iostream>

#include <util/find_symbols.h>
#include <util/i2string.h>
#include <util/simplify_expr.h>
#include <langapi/languages.h>

#define SYMB_BOUND_VAR "symb_bound#"

void linrank_domaint::initialize(valuet &value)
{
	templ_valuet &v = static_cast<templ_valuet&>(value);
	v.resize(templ.size());
	for(unsigned row = 0; row<templ.size(); row++)
		v[row] = false_exprt();
}

exprt linrank_domaint::get_not_constraints(const linrank_domaint::templ_valuet &value,
			    exprt::operandst &cond_exprs,
			    linrank_domaint::pre_post_valuest &value_exprs)
{
	cond_exprs.resize(value.size());
	value_exprs.resize(value.size());

	for(unsigned row = 0; row<templ.size(); row++)
	{
		value_exprs[row] = templ[row].expr;
		rename(value_exprs[row]);

		exprt sum_first = value[row].d;
		exprt sum_second = value[row].d;
		for(int i = 0; i < value[row].c.size(); ++i)
		{
			sum_first = plus_exprt(sum_first, mult_exprt(value[row].c[i], templ[row].expr[i].first));
			sum_second = plus_exprt(sum_second, mult_exprt(value[row].c[i], templ[row].expr[i].second));
		}

		exprt bounded = binary_relation_exprt(sum_first, ID_g, constant_exprt(0, value[row].d.type()));
		exprt decreasing = binary_relation_exprt(sum_first, ID_g, sum_second);

		cond_exprs[row] = implies_exprt(and_exprt(templ[row].pre_guard, templ[row].post_guard),
				not_exprt(and_exprt(bounded, decreasing)));
	}

	return conjunction(cond_exprs);
}

exprt linrank_domaint::get_row_symb_contraint(linrank_domaint::row_valuet &symb_values, // contains vars c and d
			       const linrank_domaint::rowt &row,
			       linrank_domaint::pre_post_valuest &values)
{
	symb_values.c.resize(values.size());

	symb_values.d = symbol_exprt(SYMB_BOUND_VAR+"d", values[0].first.type());
	exprt sum_first = symb_values.d;
	exprt sum_second = symb_values.d;
	for(int i = 0; i < symb_values.c.size(); ++i)
	{
		symb_values.c[i] = symbol_exprt(SYMB_BOUND_VAR+i2string(i), values[i].first.type());
		sum_first = plus_exprt(sum_first, mult_exprt(symb_values.c[i], values[i].first));
		sum_second = plus_exprt(sum_second, mult_exprt(symb_values.c[i], values[i].second));
	}

	exprt bounded = binary_relation_exprt(sum_first, ID_g, constant_exprt(0, symb_values.d.type()));
	exprt decreasing = binary_relation_exprt(sum_first, ID_g, sum_second);

	return implies_exprt(and_exprt(templ[row].pre_guard, templ[row].post_guard),
			and_exprt(bounded, decreasing));
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

void linrank_domaint::output_value(std::ostream &out, const valuet &value,
  const namespacet &ns)
{
  const templ_valuet &v = static_cast<const templ_valuet &>(value);
  for(unsigned row = 0; row<templ.size(); row++)
  {
    const template_rowt &templ_row = templ[row];
    switch(templ_row.kind)
    {
    case LOOP:
      out << "(LOOP) [ " << from_expr(ns,"",templ_row.pre_guard) << " | ";
      out << from_expr(ns,"",templ_row.post_guard) << " ] ===> " << std::endl << "       ";
      break;
//    case IN: out << "(IN)   "; break;
//    case OUT: case OUTL: out << "(OUT)  "; break;
    default: assert(false);
    }
    out << "( " << from_expr(ns,"",templ_row.expr) << " <= " << from_expr(ns,"",v[row]) << " )" << std::endl;
  }
}

void linrank_domaint::output_domain(std::ostream &out, const namespacet &ns)
{
  for(unsigned row = 0; row<templ.size(); row++)
  {
    const template_rowt &templ_row = templ[row];
    switch(templ_row.kind)
    {
    case LOOP:
      out << "(LOOP) [ " << from_expr(ns,"",templ_row.pre_guard) << " | ";
      out << from_expr(ns,"",templ_row.post_guard) << " ] ===> " << std::endl << "      ";
      break;
//    case IN:
//      out << "(IN)   ";
//      out << from_expr(ns,"",templ_row.pre_guard) << " ===> " << std::endl << "      ";
//      break;
//    case OUT: case OUTL:
//      out << "(OUT)  ";
//      out << from_expr(ns,"",templ_row.post_guard) << " ===> " << std::endl << "      ";
//      break;
    default: assert(false);
    }
    out << "( " <<
        from_expr(ns,"",templ_row.expr) << " <= CONST )" << std::endl;
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
		project_row_on_kind(v,row,LOOP,c);
		assert(templ[row].kind == LOOP);
		c.push_back(binary_relation_exprt(templ[row].expr,ID_le,v[row]));
	}
	result = conjunction(c);
}

void linrank_domaint::project_on_inout(const valuet &value, exprt &result)
{
	result = true_exprt();
}

void linrank_domaint::project_on_vars(const valuet &value, const var_sett &vars, exprt &result)
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

		c.push_back(binary_relation_exprt(templ_row.expr,ID_le,v[row]));
	}
	result = conjunction(c);
}

void linrank_domaint::add_template(templatet &templ,
					      const var_specst &var_specs,
					      const namespacet &ns)
{
	templ.reserve(templ.size()+var_specs.size());

	for(var_specst::const_iterator v = var_specs.begin();
				v!=var_specs.end(); v++)
	{
		if(v->kind!=LOOP) continue;

		templ.push_back(template_rowt());
		template_rowt &templ_row = templ.back();
		templ_row.expr = v->var;
		templ_row.pre_guard = v->pre_guard;
		templ_row.post_guard = v->post_guard;
		templ_row.kind = v->kind;
	}
}
