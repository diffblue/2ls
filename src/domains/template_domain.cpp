#include "template_domain.h"

#include <iostream>

#include <util/find_symbols.h>
#include <util/arith_tools.h>
#include <util/ieee_float.h>
#include <util/i2string.h>
#include <util/simplify_expr.h>
#include <langapi/languages.h>

#define SYMB_BOUND_VAR "symb_bound#"

/*******************************************************************\

Function: template_domaint::initialize

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void template_domaint::initialize(valuet &value)
{
  templ_valuet &v = static_cast<templ_valuet&>(value);
  v.resize(templ.size());
  for(unsigned row = 0; row<templ.size(); row++)
  {
    if(templ[row].kind==IN) v[row] = true_exprt(); //marker for oo
    else v[row] = false_exprt(); //marker for -oo
  }
}

/*******************************************************************\

Function: template_domaint::between

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

template_domaint::row_valuet template_domaint::between(
  const row_valuet &lower, const row_valuet &upper)
{
  if(lower.type()==upper.type() && 
     (lower.type().id()==ID_signedbv || lower.type().id()==ID_unsignedbv))
  {
    mp_integer vlower, vupper;
    to_integer(lower, vlower);
    to_integer(upper, vupper);
    assert(vupper>=vlower);
    if(vlower+1==vupper) return from_integer(vlower,lower.type()); //floor
    return from_integer((vupper+vlower)/2,lower.type());
  }
  if(lower.type().id()==ID_floatbv && upper.type().id()==ID_floatbv)
  {
    ieee_floatt vlower(to_constant_expr(lower));
    ieee_floatt vupper(to_constant_expr(upper));
    if(vlower.get_sign()==vupper.get_sign()) 
    {
      mp_integer plower = vlower.pack(); //compute "median" float number
      mp_integer pupper = vupper.pack();
      //assert(pupper>=plower);
      ieee_floatt res;
      res.unpack((plower+pupper)/2); //...by computing integer mean
      return res.to_expr();
    }
    ieee_floatt res;
    res.make_zero();
    return res.to_expr();
  }
  assert(false); //types do not match or are not supported
}

/*******************************************************************\

Function: template_domaint::leq

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool template_domaint::less_than(const row_valuet &v1, const row_valuet &v2)
{
  if(v1.type()==v2.type() && 
     (v1.type().id()==ID_signedbv || v1.type().id()==ID_unsignedbv))
  {
    mp_integer vv1, vv2;
    to_integer(v1, vv1);
    to_integer(v2, vv2);
    return vv1<vv2;
  }
  if(v1.type().id()==ID_floatbv && v2.type().id()==ID_floatbv)
  {
    ieee_floatt vv1(to_constant_expr(v1));
    ieee_floatt vv2(to_constant_expr(v2));
    return vv1<vv2;
  }
  assert(false); //types do not match or are not supported
}

/*******************************************************************\

Function: template_domaint::get_row_pre_constraint

  Inputs:

 Outputs:

 Purpose: pre_guard ==> row_expr <= row_value

\*******************************************************************/

exprt template_domaint::get_row_constraint(const rowt &row, 
  const row_valuet &row_value)
{
  assert(row<templ.size());
  kindt k = templ[row].kind;
  if(k==OUT || k==OUTL) return true_exprt();
  if(is_row_value_neginf(row_value)) return false_exprt();
  if(is_row_value_inf(row_value)) return true_exprt();
  return binary_relation_exprt(templ[row].expr,ID_le,row_value);
}

exprt template_domaint::get_row_pre_constraint(const rowt &row, 
  const row_valuet &row_value)
{
  assert(row<templ.size());
  const template_rowt &templ_row = templ[row];
  kindt k = templ_row.kind;
  if(k==OUT || k==OUTL) return true_exprt();
  if(is_row_value_neginf(row_value)) 
    return implies_exprt(templ_row.pre_guard, false_exprt());
  if(is_row_value_inf(row_value)) 
   return implies_exprt(templ_row.pre_guard, true_exprt());
  return implies_exprt(templ_row.pre_guard, 
    binary_relation_exprt(templ_row.expr,ID_le,row_value));
}


exprt template_domaint::get_row_pre_constraint(const rowt &row, 
  const templ_valuet &value)
{
  assert(value.size()==templ.size());
  return get_row_pre_constraint(row,value[row]);
}

/*******************************************************************\

Function: template_domaint::get_row_post_constraint

  Inputs:

 Outputs:

 Purpose: row_expr <= row_value

\*******************************************************************/

exprt template_domaint::get_row_post_constraint(const rowt &row, 
  const row_valuet &row_value)
{
  assert(row<templ.size());
  const template_rowt &templ_row = templ[row];
  if(templ_row.kind==IN) return true_exprt();
  if(is_row_value_neginf(row_value)) 
    return implies_exprt(templ_row.post_guard, false_exprt());
  if(is_row_value_inf(row_value)) 
    return implies_exprt(templ_row.post_guard, true_exprt());
  return implies_exprt(templ_row.post_guard, 
    binary_relation_exprt(templ_row.expr,ID_le,row_value));
}

exprt template_domaint::get_row_post_constraint(const rowt &row, 
  const templ_valuet &value)
{
  assert(value.size()==templ.size());
  return get_row_post_constraint(row,value[row]);
}

/*******************************************************************\

Function: template_domaint::to_pre_constraints

  Inputs:

 Outputs:

 Purpose: /\_all_rows ( pre_guard ==> (row_expr <= row_value) )

\*******************************************************************/

exprt template_domaint::to_pre_constraints(const templ_valuet &value)
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

Function: template_domaint::make_not_post_constraints

  Inputs:

 Outputs:

 Purpose: for all rows !(post_guard ==> (row_expr <= row_value))
          to be connected disjunctively

\*******************************************************************/

void template_domaint::make_not_post_constraints(const templ_valuet &value,
  exprt::operandst &cond_exprs, 
  exprt::operandst &value_exprs)
{
  assert(value.size()==templ.size());
  cond_exprs.resize(templ.size());
  value_exprs.resize(templ.size());

  exprt::operandst c; 
  for(unsigned row = 0; row<templ.size(); row++)
  {
    value_exprs[row] = templ[row].expr;
    cond_exprs[row] = not_exprt(get_row_post_constraint(row,value));
  }
}

/*******************************************************************\

Function: template_domaint::get_row_symb_value

  Inputs:

 Outputs:

 Purpose: generates symbolic value symbol

\*******************************************************************/

exprt template_domaint::get_row_symb_value(const rowt &row)
{
  assert(row<templ.size());
  return symbol_exprt(SYMB_BOUND_VAR+i2string(row),templ[row].expr.type());
}

/*******************************************************************\

Function: template_domaint::get_row_symb_pre_constraint

  Inputs:

 Outputs:

 Purpose: pre_guard ==> (row_expr <= symb_value)

\*******************************************************************/

exprt template_domaint::get_row_symb_pre_constraint(const rowt &row, 
  const row_valuet &row_value)
{
  assert(row<templ.size());
  const template_rowt &templ_row = templ[row];
  if(templ_row.kind==OUT || templ_row.kind==OUTL) return true_exprt();
  return implies_exprt(templ_row.pre_guard, 
    binary_relation_exprt(templ_row.expr,ID_le,get_row_symb_value(row)));
}

/*******************************************************************\

Function: template_domaint::get_row_symb_post_constraint

  Inputs:

 Outputs:

 Purpose: post_guard && (row_expr >= row_symb_value)  (!!!)

\*******************************************************************/

exprt template_domaint::get_row_symb_post_constraint(const rowt &row)
{
  assert(row<templ.size());
  const template_rowt &templ_row = templ[row];
  if(templ_row.kind==IN) return true_exprt();
  return and_exprt(templ_row.post_guard,
    binary_relation_exprt(templ_row.expr,ID_ge,get_row_symb_value(row)));
}


/*******************************************************************\

Function: template_domaint::to_symb_pre_constraints

  Inputs:

 Outputs:

 Purpose: pre_guard ==> (row_expr <= symb_row_value)

\*******************************************************************/

exprt template_domaint::to_symb_pre_constraints(const templ_valuet &value)
{
  assert(value.size()==templ.size());
  exprt::operandst c; 
  for(unsigned row = 0; row<templ.size(); row++)
  {
    c.push_back(get_row_symb_pre_constraint(row,value[row]));
  }
  return conjunction(c); 
}

/*******************************************************************\

Function: template_domaint::to_symb_pre_constraints

  Inputs:

 Outputs:

 Purpose: pre_guard ==> (row_expr <= symb_row_value)

\*******************************************************************/

exprt template_domaint::to_symb_pre_constraints(const templ_valuet &value,
						const std::set<rowt> &symb_rows)
{
  assert(value.size()==templ.size());
  exprt::operandst c; 
  for(unsigned row = 0; row<templ.size(); row++)
  {
    if(symb_rows.find(row)!=symb_rows.end())
      c.push_back(get_row_symb_pre_constraint(row,value[row]));
    else
      c.push_back(get_row_pre_constraint(row,value[row]));
  }
  return conjunction(c); 
}

/*******************************************************************\

Function: template_domaint::to_symb_post_constraints

  Inputs:

 Outputs:

 Purpose: post_guard ==> (row_expr >= symb_row_value)

\*******************************************************************/

exprt template_domaint::to_symb_post_constraints()
{
  exprt::operandst c; 
  for(unsigned row = 0; row<templ.size(); row++)
  {
    c.push_back(get_row_symb_post_constraint(row));
  }
  return conjunction(c); 
}

/*******************************************************************\

Function: template_domaint::get_row_symb_value_constraint

  Inputs:

 Outputs:

 Purpose: row_value <= symb_row_value

\*******************************************************************/

exprt template_domaint::get_row_symb_value_constraint(const rowt &row, 
						const row_valuet &row_value)
{
  if(is_row_value_neginf(row_value)) return false_exprt();
  if(is_row_value_inf(row_value)) return true_exprt();
  return binary_relation_exprt(row_value,ID_le,get_row_symb_value(row));
}


/*******************************************************************\

Function: template_domaint::get_row_value

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

template_domaint::row_valuet template_domaint::get_row_value(
  const rowt &row, const templ_valuet &value)
{
  assert(row<value.size());
  assert(value.size()==templ.size());
  return value[row];
}

/*******************************************************************\

Function: template_domaint::project_on_loops

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void template_domaint::project_on_loops(const valuet &value, exprt &result)
{
  const templ_valuet &v = static_cast<const templ_valuet &>(value);
  assert(v.size()==templ.size());
  exprt::operandst c;
  c.reserve(templ.size());
  for(unsigned row = 0; row<templ.size(); row++)
  {
    if(templ[row].kind!=LOOP) continue;
    const row_valuet &row_v = v[row];
    if(is_row_value_neginf(row_v)) c.push_back(false_exprt());
    else if(is_row_value_inf(row_v)) c.push_back(true_exprt());
    else c.push_back(binary_relation_exprt(templ[row].expr,ID_le,row_v));
  }
  result = conjunction(c);
}

/*******************************************************************\

Function: template_domaint::project_on_inout

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void template_domaint::project_on_inout(const valuet &value, exprt &result)
{
  const templ_valuet &v = static_cast<const templ_valuet &>(value);
  assert(v.size()==templ.size());
  exprt::operandst c;
  c.reserve(templ.size());
  for(unsigned row = 0; row<templ.size(); row++)
  {
    const template_rowt &templ_row = templ[row];
    if(templ_row.kind==LOOP || templ_row.kind==OUTL) continue;
    const row_valuet &row_v = v[row];
    if(is_row_value_neginf(row_v)) c.push_back(false_exprt());
    else if(is_row_value_inf(row_v)) c.push_back(true_exprt());
    else c.push_back(binary_relation_exprt(templ_row.expr,ID_le,row_v));
  }
  result = conjunction(c);
}

/*******************************************************************\

Function: template_domaint::set_row_value

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void template_domaint::set_row_value(
  const rowt &row, const template_domaint::row_valuet &row_value, templ_valuet &value)
{
  assert(row<value.size());
  assert(value.size()==templ.size());
  value[row] = row_value;
}


/*******************************************************************\

Function: template_domaint::get_row_max_value

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

template_domaint::row_valuet template_domaint::get_max_row_value(
  const template_domaint::rowt &row)
{
  const template_rowt &templ_row = templ[row];
  if(templ_row.expr.type().id()==ID_signedbv)
  {
    return to_signedbv_type(templ_row.expr.type()).largest_expr();
  }
  if(templ_row.expr.type().id()==ID_unsignedbv)
  {
    return to_unsignedbv_type(templ_row.expr.type()).largest_expr();
  }
  if(templ_row.expr.type().id()==ID_floatbv) 
  {
    ieee_floatt max;
    max.make_fltmax();
    return max.to_expr();
  }
  assert(false); //type not supported
}

/*******************************************************************\

Function: template_domaint::get_row_max_value

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

template_domaint::row_valuet template_domaint::get_min_row_value(
  const template_domaint::rowt &row)
{
  const template_rowt &templ_row = templ[row];
  if(templ_row.expr.type().id()==ID_signedbv)
  {
    return to_signedbv_type(templ_row.expr.type()).smallest_expr();
  }
  if(templ_row.expr.type().id()==ID_unsignedbv)
  {
    return to_unsignedbv_type(templ_row.expr.type()).smallest_expr();
  }
  if(templ_row.expr.type().id()==ID_floatbv) 
  {
    ieee_floatt min;
    min.make_fltmin();
    return min.to_expr();
  }
  assert(false); //type not supported
}

/*******************************************************************\

Function: template_domaint::output_value

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void template_domaint::output_value(std::ostream &out, const valuet &value, 
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
      out << from_expr(ns,"",templ_row.post_guard) << " ] ===> " << std::endl << "       ";
      break;
    case IN: out << "(IN)   "; break;
    case OUT: case OUTL: out << "(OUT)  "; break;
    default: assert(false);
    }
    out << "( " << from_expr(ns,"",templ_row.expr) << " <= ";
    if(is_row_value_neginf(v[row])) out << "-oo";
    else if(is_row_value_inf(v[row])) out << "oo";
    else out << from_expr(ns,"",v[row]);
    out << " )" << std::endl;
  }
}

/*******************************************************************\

Function: template_domaint::output_domain

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void template_domaint::output_domain(std::ostream &out, const namespacet &ns) const
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
    case IN: out << "(IN)   "; break;
    case OUT: case OUTL:
      out << "(OUT)  "; 
      out << from_expr(ns,"",templ_row.post_guard) << " ===> " << std::endl << "      ";
      break;
    default: assert(false);
    }
    out << "( " << 
        from_expr(ns,"",templ_row.expr) << " <= CONST )" << std::endl;
  }
}

/*******************************************************************\

Function: template_domaint::template_size

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

unsigned template_domaint::template_size()
{
  return templ.size();
}

/*******************************************************************\

Function: template_domaint::is_row_value_neginf

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool template_domaint::is_row_value_neginf(const row_valuet & row_value) const
{
  return row_value.get(ID_value)==ID_false;
}

/*******************************************************************\

Function: template_domaint::is_row_value_inf

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool template_domaint::is_row_value_inf(const row_valuet & row_value) const
{
  return row_value.get(ID_value)==ID_true;
}

/*******************************************************************\

Function: extend_expr_types

  Inputs:

 Outputs:

 Purpose: increases bitvector sizes such that there are no overflows

\*******************************************************************/

void extend_expr_types(exprt &expr)
{
  if(expr.id()==ID_symbol) return;
  if(expr.id()==ID_unary_minus)
  {
    extend_expr_types(expr.op0());
    typet new_type = expr.op0().type();
    if(new_type.id()==ID_signedbv) 
    {
      signedbv_typet &new_typebv = to_signedbv_type(new_type);
      new_typebv.set_width(new_typebv.get_width()+1); 
    }
    else if(new_type.id()==ID_unsignedbv) 
    {
      unsignedbv_typet &old_type = to_unsignedbv_type(new_type);
      new_type = signedbv_typet(old_type.get_width()+1); 
    }
    expr = unary_minus_exprt(typecast_exprt(expr.op0(),new_type),new_type);
    return;
  }
  if(expr.id()==ID_plus || expr.id()==ID_minus)
  {
    extend_expr_types(expr.op0());
    extend_expr_types(expr.op1());
    unsigned size0 = 0, size1  = 0;
    if(expr.op0().type().id()==ID_signedbv) 
      size0 =  to_signedbv_type(expr.op0().type()).get_width();
    if(expr.op0().type().id()==ID_unsignedbv) 
      size0 =  to_unsignedbv_type(expr.op0().type()).get_width();
    if(expr.op1().type().id()==ID_signedbv) 
      size1 =  to_signedbv_type(expr.op1().type()).get_width();
    if(expr.op1().type().id()==ID_unsignedbv) 
      size1 =  to_unsignedbv_type(expr.op1().type()).get_width();
    assert(size0>0); assert(size1>0); //TODO: implement floats
    typet new_type = expr.op0().type();
    if(expr.op0().type().id()==expr.op1().type().id())
    {
     if(new_type.id()==ID_signedbv) 
       to_signedbv_type(new_type).set_width(std::max(size0,size1)+1);
     else if(new_type.id()==ID_unsignedbv) 
     {
       if(expr.id()==ID_minus) 
         new_type = signedbv_typet(std::max(size0,size1)+1);
       else 
         to_unsignedbv_type(new_type).set_width(std::max(size0,size1)+1);
     }
    }
    else
    {
     if(new_type.id()==ID_signedbv) 
       to_signedbv_type(new_type).set_width(size0<=size1 ? size1+2 : size0+1);
     else if(new_type.id()==ID_unsignedbv) 
       new_type = signedbv_typet(size1<=size0 ? size0+2 : size1+1);
    }
    if(expr.id()==ID_plus)
      expr = plus_exprt(typecast_exprt(expr.op0(),new_type),typecast_exprt(expr.op1(),new_type));
    else if(expr.id()==ID_minus)
      expr = minus_exprt(typecast_exprt(expr.op0(),new_type),typecast_exprt(expr.op1(),new_type));
    return;
  }
  //TODO: implement mult
  assert(false);
}

/*******************************************************************\

Function: make_interval_template

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void template_domaint::add_interval_template(templatet &templ, 
					      const var_specst &var_specs,
					      const namespacet &ns)
{
  unsigned size = 2*var_specs.size();
  templ.reserve(templ.size()+size);
  
  for(var_specst::const_iterator v = var_specs.begin(); 
      v!=var_specs.end(); v++)
  {
    if(v->kind==IN) continue; //TODO: must be done in caller (for preconditions, e.g.)

    // x
    {
      templ.push_back(template_rowt());
      template_rowt &templ_row = templ.back();
      templ_row.expr = v->var;
      templ_row.pre_guard = v->pre_guard;
      templ_row.post_guard = v->post_guard;
      templ_row.kind = v->kind;
    }

    // -x
    {
      templ.push_back(template_rowt());
      template_rowt &templ_row = templ.back();
      unary_minus_exprt um_expr(v->var,v->var.type());
      extend_expr_types(um_expr);
      templ_row.expr = um_expr;
      templ_row.pre_guard = v->pre_guard;
      templ_row.post_guard = v->post_guard;
      templ_row.kind = v->kind;
    }
  }
}

/*******************************************************************\

Function: make_zone_template

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void template_domaint::add_zone_template(templatet &templ, 
					  const var_specst &var_specs,
					  const namespacet &ns)
{ 
  unsigned size = 2*var_specs.size()+var_specs.size()*(var_specs.size()-1);
  templ.reserve(templ.size()+size);
  
  for(var_specst::const_iterator v1 = var_specs.begin(); 
      v1!=var_specs.end(); v1++)
  {
    if(v1->kind!=IN) //TODO: must be done in caller (for preconditions, e.g.)
    {
      // x
      {
	templ.push_back(template_rowt());
	template_rowt &templ_row = templ.back();
	templ_row.expr = v1->var;
	templ_row.pre_guard = v1->pre_guard;
	templ_row.post_guard = v1->post_guard;
	templ_row.kind = v1->kind;
      }

      // -x
      {
	templ.push_back(template_rowt());
	template_rowt &templ_row = templ.back();
	unary_minus_exprt um_expr(v1->var,v1->var.type());
	extend_expr_types(um_expr);
	templ_row.expr = um_expr;
	templ_row.pre_guard = v1->pre_guard;
	templ_row.post_guard = v1->post_guard;
	templ_row.kind = v1->kind;
      }
    }

    var_specst::const_iterator v2 = v1; v2++;
    for(; v2!=var_specs.end(); v2++)
    {
      kindt k = domaint::merge_kinds(v1->kind,v2->kind);
      if(k==IN) continue; //TODO: must be done in caller (for preconditions, e.g.)

      exprt pre_g = and_exprt(v1->pre_guard,v2->pre_guard);
      exprt post_g = and_exprt(v1->post_guard,v2->post_guard);
      simplify(pre_g,ns);
      simplify(post_g,ns);

      // x1 - x2
      {
	templ.push_back(template_rowt());
	template_rowt &templ_row = templ.back();
        minus_exprt m_expr(v1->var,v2->var);
        extend_expr_types(m_expr);
	templ_row.expr = m_expr;
	templ_row.pre_guard = pre_g;
	templ_row.post_guard = post_g;
	templ_row.kind = k;
      }

      // x2 - x1
      {
	templ.push_back(template_rowt());
	template_rowt &templ_row = templ.back();
        minus_exprt m_expr(v2->var,v1->var);
        extend_expr_types(m_expr);
	templ_row.expr = m_expr;
	templ_row.pre_guard = pre_g;
	templ_row.post_guard = post_g;
	templ_row.kind = k;
      }
    }
  }
}

/*******************************************************************\

Function: make_octagon_template

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void template_domaint::add_octagon_template(templatet &templ,
					     const var_specst &var_specs,
					     const namespacet &ns)
{
  unsigned size = 2*var_specs.size()+2*var_specs.size()*(var_specs.size()-1);
  templ.reserve(templ.size()+size);
  
  for(var_specst::const_iterator v1 = var_specs.begin(); 
      v1!=var_specs.end(); v1++)
  {
    if(v1->kind!=IN) //TODO: must be done in caller (for preconditions, e.g.)
    {
      // x
      {
	templ.push_back(template_rowt());
	template_rowt &templ_row = templ.back();
	templ_row.expr = v1->var;
	templ_row.pre_guard = v1->pre_guard;
	templ_row.post_guard = v1->post_guard;
	templ_row.kind = v1->kind;
      }

      // -x
      {
	templ.push_back(template_rowt());
	template_rowt &templ_row = templ.back();
	unary_minus_exprt um_expr(v1->var,v1->var.type());
	extend_expr_types(um_expr);
	templ_row.expr = um_expr;
	templ_row.pre_guard = v1->pre_guard;
	templ_row.post_guard = v1->post_guard;
	templ_row.kind = v1->kind;
      }
    }

    var_specst::const_iterator v2 = v1; v2++;
    for(; v2!=var_specs.end(); v2++)
    {
      kindt k = domaint::merge_kinds(v1->kind,v2->kind);
      if(k==IN) continue; //TODO: must be done in caller (for preconditions, e.g.)

      exprt pre_g = and_exprt(v1->pre_guard,v2->pre_guard);
      exprt post_g = and_exprt(v1->post_guard,v2->post_guard);
      simplify(pre_g,ns);
      simplify(post_g,ns);

      // x1 - x2
      {
	templ.push_back(template_rowt());
	template_rowt &templ_row = templ.back();
        minus_exprt m_expr(v1->var,v2->var);
        extend_expr_types(m_expr);
	templ_row.expr = m_expr;
	templ_row.pre_guard = pre_g;
	templ_row.post_guard = post_g;
	templ_row.kind = k;
      }

      // -x1 + x2
      {
	templ.push_back(template_rowt());
	template_rowt &templ_row = templ.back();
        minus_exprt m_expr(v2->var,v1->var);
        extend_expr_types(m_expr);
	templ_row.expr = m_expr;
	templ_row.pre_guard = pre_g;
	templ_row.post_guard = post_g;
	templ_row.kind = k;
      }

      // -x1 - x2
      {
	templ.push_back(template_rowt());
	template_rowt &templ_row = templ.back();
        minus_exprt p_expr(unary_minus_exprt(v1->var,v1->var.type()),v2->var);
        extend_expr_types(p_expr);
	templ_row.expr = p_expr;
	templ_row.pre_guard = pre_g;
	templ_row.post_guard = post_g;
	templ_row.kind = k;
      }

      // x1 + x2
      {
	templ.push_back(template_rowt());
	template_rowt &templ_row = templ.back();
        plus_exprt p_expr(v1->var,v2->var);
        extend_expr_types(p_expr);
	templ_row.expr = p_expr;
	templ_row.pre_guard = pre_g;
	templ_row.post_guard = post_g;
	templ_row.kind = k;
      }
    }
  }

}

/*******************************************************************\

Function: simplify_const

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

mp_integer simplify_const_int(const exprt &expr)
{
  if(expr.id()==ID_constant) 
  {
    mp_integer v;
    to_integer(expr, v);
    return v;
  }
  if(expr.id()==ID_typecast) 
  {
    const exprt &op0 = expr.op0();
    assert(op0.type().id()==ID_signedbv || op0.type().id()==ID_unsignedbv);
    return simplify_const_int(op0);
  }
  if(expr.id()==ID_unary_minus) return -simplify_const_int(expr.op0());
  if(expr.id()==ID_plus) return simplify_const_int(expr.op0())+simplify_const_int(expr.op1());
  if(expr.id()==ID_minus) return simplify_const_int(expr.op0())-simplify_const_int(expr.op1());
  if(expr.id()==ID_mult) return simplify_const_int(expr.op0())*simplify_const_int(expr.op1());  
  if(expr.id()==ID_symbol) return 0; //default value if not substituted in expr
  assert(false); //not implemented
}

ieee_floatt simplify_const_float(const exprt &expr)
{
  if(expr.id()==ID_constant) 
  {
    ieee_floatt v(to_constant_expr(expr));
    return v;
  }
  if(expr.id()==ID_typecast) 
  {
    const exprt &op0 = expr.op0();
    if(op0.type().id()==ID_signedbv || op0.type().id()==ID_unsignedbv)
    {
      ieee_floatt v;
      v.from_integer(simplify_const_int(op0));
      return v; 
    }
    assert(false);
  }
  if(expr.id()==ID_unary_minus) 
  {
    ieee_floatt v = simplify_const_float(expr.op0());
    v.set_sign(!v.get_sign());
    return v; 
  }
  if(expr.id()==ID_plus) 
  {
    ieee_floatt v1 = simplify_const_float(expr.op0());
    ieee_floatt v2 = simplify_const_float(expr.op1());
    v1 += v2;
    return v1; 
  }
  if(expr.id()==ID_minus)
  {
    ieee_floatt v1 = simplify_const_float(expr.op0());
    ieee_floatt v2 = simplify_const_float(expr.op1());
    v1 -= v2;
    return v1; 
  }
  if(expr.id()==ID_mult)
  {
    ieee_floatt v1 = simplify_const_float(expr.op0());
    ieee_floatt v2 = simplify_const_float(expr.op1());
    v1 *= v2;
    return v1; 
  }
  if(expr.id()==ID_symbol)  //default value if not substituted in expr
  {
    ieee_floatt v;
    v.make_zero();
    return v; 
  }
  assert(false); //not implemented
}

constant_exprt simplify_const(const exprt &expr)
{
  if(expr.id()==ID_constant) return to_constant_expr(expr);
  //  if(expr.id()==ID_typecast) return to_constant_expr(expr.op0());
  if(expr.type().id()==ID_signedbv) 
  {
    mp_integer res = simplify_const_int(expr);
    const signedbv_typet &type = to_signedbv_type(expr.type());
    assert(res>=type.smallest());
    assert(res<=type.largest());
    return to_constant_expr(from_integer(res,expr.type()));
  }
  if(expr.type().id()==ID_unsignedbv)
  {
    mp_integer res = simplify_const_int(expr);
    const unsignedbv_typet &type = to_unsignedbv_type(expr.type());
    assert(res>=type.smallest());
    assert(res<=type.largest());
    return to_constant_expr(from_integer(res,expr.type()));
  }
  if(expr.type().id()==ID_floatbv)
  {
    return to_constant_expr(simplify_const_float(expr).to_expr());
  }
  assert(false); //type not supported
}
