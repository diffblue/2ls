#include "template_domain.h"

#include <iostream>

#include <util/find_symbols.h>
#include <util/arith_tools.h>
#include <util/ieee_float.h>
#include <util/simplify_expr.h>
#include <langapi/languages.h>

/*******************************************************************\

Function: template_domaint::bottom

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void template_domaint::bottom(valuet &value)
{
  value.resize(templ.size());
  for(unsigned row = 0; row<templ.size(); row++)
  {
    value[row] = false_exprt(); //marker for -oo
  }
}

/*******************************************************************\

Function: template_domaint::set_to_top

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void template_domaint::set_to_top(const var_listt &top_vars, valuet &value)
{
  assert(value.size()==templ.size());
  
  find_symbols_sett top_symbols;
  for(var_listt::const_iterator 
      it=top_vars.begin();
      it!=top_vars.end(); 
      ++it)
  {
    top_symbols.insert(it->get_identifier());
  }
  
  for(unsigned row = 0; row<templ.size(); row++)
  {
    const exprt &row_expr=templ.rows[row];
  
    if(has_symbol(row_expr, top_symbols))
    {
      value[row] = true_exprt(); //get_max_row_value(row); //marker for oo
    }
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
    return from_integer((vupper-vlower)/2,lower.type());
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
      res.unpack((plower-pupper)/2); //...by computing integer mean
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

 Purpose:

\*******************************************************************/

exprt template_domaint::get_row_constraint(const rowt &row, const row_valuet &row_value)
{
  assert(row<templ.size());
  kindt k = templ.kinds[row];
  if(k==OUT || k==OUTL) return true_exprt();
  if(is_row_value_neginf(row_value)) return false_exprt();
  if(is_row_value_inf(row_value)) return true_exprt();
  return binary_relation_exprt(templ.rows[row],ID_le,row_value);
}

exprt template_domaint::get_row_pre_constraint(const rowt &row, const row_valuet &row_value)
{
  assert(row<templ.size());
  kindt k = templ.kinds[row];
  if(k==OUT || k==OUTL) return true_exprt();
  if(is_row_value_neginf(row_value)) return implies_exprt(templ.pre_guards[row], false_exprt());
  if(is_row_value_inf(row_value)) return true_exprt();
  return implies_exprt(templ.pre_guards[row], binary_relation_exprt(templ.rows[row],ID_le,row_value));
}


exprt template_domaint::get_row_pre_constraint(const rowt &row, const valuet &value)
{
  assert(value.size()==templ.size());
  return get_row_pre_constraint(row,value[row]);
}

/*******************************************************************\

Function: template_domaint::get_row_post_constraint

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt template_domaint::get_row_post_constraint(const rowt &row, const row_valuet &row_value)
{
  assert(row<templ.size());
  if(templ.kinds[row]==IN) return true_exprt();
  if(is_row_value_neginf(row_value)) return implies_exprt(templ.post_guards[row], false_exprt());
  if(is_row_value_inf(row_value)) return true_exprt();
  return implies_exprt(templ.post_guards[row], binary_relation_exprt(templ.rows[row],ID_le,row_value));
}

exprt template_domaint::get_row_post_constraint(const rowt &row, const valuet &value)
{
  assert(value.size()==templ.size());
  return get_row_post_constraint(row,value[row]);
}

/*******************************************************************\

Function: template_domaint::to_pre_constraints

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt template_domaint::to_pre_constraints(const valuet &value)
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

 Purpose:

\*******************************************************************/

void template_domaint::make_not_post_constraints(const valuet &value,
  exprt::operandst &cond_exprs, 
  exprt::operandst &value_exprs)
{
  assert(value.size()==templ.size());
  cond_exprs.resize(templ.size());
  value_exprs.resize(templ.size());

  exprt::operandst c; 
  for(unsigned row = 0; row<templ.size(); row++)
  {
    value_exprs[row] = templ.rows[row];
    cond_exprs[row] = not_exprt(get_row_post_constraint(row,value));
  }
}

/*******************************************************************\

Function: template_domaint::get_row_value

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

template_domaint::row_valuet template_domaint::get_row_value(
  const rowt &row, const valuet &value)
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
  assert(value.size()==templ.size());
  exprt::operandst c;
  c.reserve(templ.size());
  for(unsigned row = 0; row<templ.size(); row++)
  {
    if(templ.kinds[row]!=LOOP) continue;
    const row_valuet &row_value = value[row];
    if(is_row_value_neginf(row_value)) c.push_back(false_exprt());
    else if(is_row_value_inf(row_value)) c.push_back(true_exprt());
    else c.push_back(binary_relation_exprt(templ.rows[row],ID_le,row_value));
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
  assert(value.size()==templ.size());
  exprt::operandst c;
  c.reserve(templ.size());
  for(unsigned row = 0; row<templ.size(); row++)
  {
    kindt k = templ.kinds[row];
    if(k==LOOP || k==OUTL) continue;
    const row_valuet &row_value = value[row];
    if(is_row_value_neginf(row_value)) c.push_back(false_exprt());
    else if(is_row_value_inf(row_value)) c.push_back(true_exprt());
    else c.push_back(binary_relation_exprt(templ.rows[row],ID_le,row_value));
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
  const rowt &row, const template_domaint::row_valuet &row_value, valuet &value)
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
  if(templ.rows[row].type().id()==ID_signedbv)
  {
    return to_signedbv_type(templ.rows[row].type()).largest_expr();
  }
  if(templ.rows[row].type().id()==ID_unsignedbv)
  {
    return to_unsignedbv_type(templ.rows[row].type()).largest_expr();
  }
  if(templ.rows[row].type().id()==ID_floatbv) 
  {
    ieee_floatt max;
    max.make_fltmax();
    return max.to_expr();
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
  for(unsigned row = 0; row<templ.size(); row++)
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
  }
}

/*******************************************************************\

Function: template_domaint::output_template

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void template_domaint::output_template(std::ostream &out, const namespacet &ns) const
{
  for(unsigned row = 0; row<templ.size(); row++)
  {
    switch(templ.kinds[row])
    {
    case LOOP:
      out << "(LOOP) [ " << from_expr(ns,"",templ.pre_guards[row]) << " | ";
      out << from_expr(ns,"",templ.post_guards[row]) << " ] ===> " << std::endl << "      ";
      break;
    case IN: out << "(IN)   "; break;
    case OUT: case OUTL: out << "(OUT)  "; break;
    default: assert(false);
    }
    out << "( " << 
        from_expr(ns,"",templ.rows[row]) << " <= CONST )" << std::endl;
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
    if(new_type.id()==ID_unsignedbv) 
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
     if(new_type.id()==ID_unsignedbv) 
       to_unsignedbv_type(new_type).set_width(std::max(size0,size1)+1);
    }
    else
    {
     if(new_type.id()==ID_signedbv) 
       to_signedbv_type(new_type).set_width(size0<=size1 ? size1+2 : size0+1);
     if(new_type.id()==ID_unsignedbv) 
       new_type = signedbv_typet(size1<=size0 ? size0+2 : size1+1);
    }
    if(expr.id()==ID_plus)
      expr = plus_exprt(typecast_exprt(expr.op0(),new_type),typecast_exprt(expr.op1(),new_type));
    if(expr.id()==ID_minus)
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

void make_interval_template(template_domaint::templatet &templ, 
  const template_domaint::var_listt &vars,
  const template_domaint::var_guardst &pre_guards,
  const template_domaint::var_guardst &post_guards,
  const template_domaint::kindst &kinds,
  const namespacet &ns)
{
  assert(vars.size() == pre_guards.size());
  assert(vars.size() == post_guards.size());
  assert(vars.size() == kinds.size());
  unsigned size = 2*vars.size();
  templ.rows.clear(); templ.rows.reserve(size);
  templ.pre_guards.clear(); templ.pre_guards.reserve(size);
  templ.post_guards.clear(); templ.post_guards.reserve(size);
  templ.kinds.clear(); templ.kinds.reserve(size);
  
  template_domaint::var_guardst::const_iterator pre_g = pre_guards.begin();
  template_domaint::var_guardst::const_iterator post_g = post_guards.begin();
  template_domaint::kindst::const_iterator k = kinds.begin();
  for(template_domaint::var_listt::const_iterator v = vars.begin(); 
      v!=vars.end(); v++, pre_g++, post_g++, k++)
  {
    templ.rows.push_back(*v);
    unary_minus_exprt um_expr(*v,v->type());
    extend_expr_types(um_expr);
    templ.rows.push_back(um_expr); 
    for(unsigned i=0;i<2;i++) 
    {
      templ.pre_guards.push_back(*pre_g);
      templ.post_guards.push_back(*post_g);
      templ.kinds.push_back(*k);
    }
  }
  assert(templ.rows.size() == templ.pre_guards.size());
  assert(templ.rows.size() == templ.post_guards.size());
  assert(templ.rows.size() == templ.kinds.size());
}

/*******************************************************************\

Function: make_zone_template

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void make_zone_template(template_domaint::templatet &templ, 
  const template_domaint::var_listt &vars,
  const template_domaint::var_guardst &pre_guards,
  const template_domaint::var_guardst &post_guards,
  const template_domaint::kindst &kinds,
  const namespacet &ns)
{ 
  assert(vars.size() == pre_guards.size());
  assert(vars.size() == post_guards.size());
  assert(vars.size() == kinds.size());
  unsigned size = 2*vars.size()+vars.size()*(vars.size()-1);
  templ.rows.clear(); templ.rows.reserve(size);
  templ.pre_guards.clear(); templ.pre_guards.reserve(size);
  templ.post_guards.clear(); templ.post_guards.reserve(size);
  templ.kinds.clear(); templ.kinds.reserve(size);

  template_domaint::var_guardst::const_iterator pre_g1 = pre_guards.begin();
  template_domaint::var_guardst::const_iterator post_g1 = post_guards.begin();
  template_domaint::kindst::const_iterator k1 = kinds.begin();
  for(template_domaint::var_listt::const_iterator v1 = vars.begin(); 
      v1!=vars.end(); v1++, pre_g1++, post_g1++, k1++)
  {
    templ.rows.push_back(*v1); 
    unary_minus_exprt um_expr(*v1,v1->type());
    extend_expr_types(um_expr);
    templ.rows.push_back(um_expr); 
    for(unsigned i=0;i<2;i++) 
    {
      templ.pre_guards.push_back(*pre_g1);
      templ.post_guards.push_back(*post_g1);
      templ.kinds.push_back(*k1);
    }
    template_domaint::var_guardst::const_iterator pre_g2 = pre_guards.begin();
    template_domaint::var_guardst::const_iterator post_g2 = post_guards.begin();
    template_domaint::var_listt::const_iterator v2 = v1; v2++;
    template_domaint::kindst::const_iterator k2 = kinds.begin();
    for(;v2!=vars.end(); v2++, pre_g2++, post_g2++, k2++)
    {
      minus_exprt m_expr1(*v1,*v2);
      extend_expr_types(m_expr1);
      templ.rows.push_back(m_expr1);

      minus_exprt m_expr2(*v2,*v1);
      extend_expr_types(m_expr2);
      templ.rows.push_back(m_expr2);

      exprt pre_g = and_exprt(*pre_g1,*pre_g2);
      exprt post_g = and_exprt(*post_g1,*post_g2);
      simplify(pre_g,ns);
      simplify(post_g,ns);
      template_domaint::kindt k = 
        (*k1==template_domaint::OUT || *k2==template_domaint::OUT ? 
	 (*k1==template_domaint::LOOP || *k2==template_domaint::LOOP ?  template_domaint::OUTL :
          template_domaint::OUT) :
         (*k1==template_domaint::LOOP || *k2==template_domaint::LOOP ? template_domaint::LOOP : 
          template_domaint::IN));
      for(unsigned i=0;i<2;i++) 
      {
        templ.pre_guards.push_back(pre_g);
        templ.post_guards.push_back(post_g);
        templ.kinds.push_back(k);
      }    
    }
  }
  assert(templ.rows.size() == templ.pre_guards.size());
  assert(templ.rows.size() == templ.post_guards.size());
  assert(templ.rows.size() == templ.kinds.size());
}

/*******************************************************************\

Function: make_octagon_template

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void make_octagon_template(template_domaint::templatet &templ,
  const template_domaint::var_listt &vars,
  const template_domaint::var_guardst &pre_guards,
  const template_domaint::var_guardst &post_guards,
  const template_domaint::kindst &kinds,
  const namespacet &ns)
{
  assert(vars.size() == pre_guards.size());
  assert(vars.size() == post_guards.size());
  unsigned size =  2*vars.size()+2*vars.size()*(vars.size()-1);
  templ.rows.clear(); templ.rows.reserve(size);
  templ.pre_guards.clear(); templ.pre_guards.reserve(size);
  templ.post_guards.clear(); templ.post_guards.reserve(size);

  template_domaint::var_guardst::const_iterator pre_g1 = pre_guards.begin();
  template_domaint::var_guardst::const_iterator post_g1 = post_guards.begin();
  template_domaint::kindst::const_iterator k1 = kinds.begin();
  for(template_domaint::var_listt::const_iterator v1 = vars.begin(); 
      v1!=vars.end(); v1++, pre_g1++, post_g1++, k1++)
  {
    templ.rows.push_back(*v1); 
    unary_minus_exprt um_expr(*v1,v1->type());
    extend_expr_types(um_expr);
    templ.rows.push_back(um_expr); 
    for(unsigned i=0;i<2;i++) 
    {
      templ.pre_guards.push_back(*pre_g1);
      templ.post_guards.push_back(*post_g1);
      templ.kinds.push_back(*k1);
    }
    template_domaint::var_guardst::const_iterator pre_g2 = pre_guards.begin();
    template_domaint::var_guardst::const_iterator post_g2 = post_guards.begin();
    template_domaint::var_listt::const_iterator v2 = v1; v2++;
    template_domaint::kindst::const_iterator k2 = kinds.begin();
    for(;v2!=vars.end(); v2++, pre_g2++, post_g2++, k2++)
    {
      minus_exprt m_expr1(*v1,*v2);
      extend_expr_types(m_expr1);
      templ.rows.push_back(m_expr1);

      minus_exprt m_expr2(*v2,*v1);
      extend_expr_types(m_expr2);
      templ.rows.push_back(m_expr2);

      plus_exprt p_expr1(*v1,*v2);
      extend_expr_types(p_expr1);
      templ.rows.push_back(p_expr1);

      plus_exprt p_expr2(unary_minus_exprt(*v1,v1->type()),*v2);
      extend_expr_types(p_expr2);
      templ.rows.push_back(p_expr2);

      exprt pre_g = and_exprt(*pre_g1,*pre_g2);
      exprt post_g = and_exprt(*post_g1,*post_g2);
      simplify(pre_g,ns);
      simplify(post_g,ns);
      template_domaint::kindt k = 
        (*k1==template_domaint::OUT || *k2==template_domaint::OUT ? 
	 (*k1==template_domaint::LOOP || *k2==template_domaint::LOOP ?  template_domaint::OUTL :
          template_domaint::OUT) :
         (*k1==template_domaint::LOOP || *k2==template_domaint::LOOP ? template_domaint::LOOP : 
          template_domaint::IN));
      for(unsigned i=0;i<4;i++) 
      {
        templ.pre_guards.push_back(pre_g);
        templ.post_guards.push_back(post_g);
        templ.kinds.push_back(k);
      }
    }
  }
  assert(templ.rows.size() == templ.pre_guards.size());
  assert(templ.rows.size() == templ.post_guards.size());
  assert(templ.rows.size() == templ.kinds.size());
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
    if(res<type.smallest() || res>type.largest()) assert(false);
    return to_constant_expr(from_integer(res,expr.type()));
  }
  if(expr.type().id()==ID_unsignedbv)
  {
    mp_integer res = simplify_const_int(expr);
    const unsignedbv_typet &type = to_unsignedbv_type(expr.type());
    if(res<type.smallest() || res>type.largest()) assert(false);
    return to_constant_expr(from_integer(res,expr.type()));
  }
  if(expr.type().id()==ID_floatbv)
  {
    return to_constant_expr(simplify_const_float(expr).to_expr());
  }
  assert(false); //type not supported
}
