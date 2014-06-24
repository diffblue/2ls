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
  equ_valuet &v = static_cast<equ_valuet &>(value);
  v.equs.clear();
  v.disequs.clear();
}

exprt equality_domaint::get_pre_equ_constraint(unsigned index)
{
  assert(index<templ.size());
  kindt k = templ.kinds[index];
  if(k==OUT || k==OUTL) return true_exprt();
  const var_pairt &vv = templ.var_pairs[index];
  return implies_exprt(templ.pre_guards[index],equal_exprt(vv.first,vv.second));
}

exprt equality_domaint::get_post_not_equ_constraint(unsigned index)
{
  assert(index<templ.size());
  kindt k = templ.kinds[index];
  if(k==IN) return true_exprt();
  const var_pairt &vv = templ.var_pairs[index];
  return not_exprt(implies_exprt(templ.post_guards[index],equal_exprt(vv.first,vv.second)));
}

exprt equality_domaint::get_pre_disequ_constraint(unsigned index)
{
  assert(index<templ.size());
  kindt k = templ.kinds[index];
  if(k==OUT || k==OUTL) return true_exprt();
  const var_pairt &vv = templ.var_pairs[index];
  return implies_exprt(templ.pre_guards[index],notequal_exprt(vv.first,vv.second));
}

exprt equality_domaint::get_post_not_disequ_constraint(unsigned index)
{
  assert(index<templ.size());
  kindt k = templ.kinds[index];
  if(k==IN) return true_exprt();
  const var_pairt &vv = templ.var_pairs[index];
  return not_exprt(implies_exprt(templ.post_guards[index],notequal_exprt(vv.first,vv.second)));
}


/*******************************************************************\

Function: equality_domaint::project_on_loops

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void equality_domaint::project_on_loops(const valuet &value, exprt &result)
{
  const equ_valuet &_v = static_cast<const equ_valuet &>(value);
  equ_valuet v = _v;

  exprt::operandst c;
  for(unsigned index = 0; index<templ.size(); index++)
  {
    const var_pairt &vv = templ.var_pairs[index];
    //    if(templ.kinds[row]!=LOOP) continue;
    if(v.equs.same_set(vv.first,vv.second)) 
      c.push_back(equal_exprt(vv.first,vv.second));
  }

  for(index_sett::const_iterator it = v.disequs.begin(); it != v.disequs.end(); it++)
  {
    //    if(templ.kinds[row]!=LOOP) continue;
    const var_pairt &vv = templ.var_pairs[*it];
    c.push_back(notequal_exprt(vv.first,vv.second));
  }
  result = conjunction(c);
}

/*******************************************************************\

Function: equality_domaint::project_on_inout

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void equality_domaint::project_on_inout(const valuet &value, exprt &result)
{
  const equ_valuet &_v = static_cast<const equ_valuet &>(value);
  equ_valuet v = _v;

  exprt::operandst c;
  for(unsigned index = 0; index<templ.size(); index++)
  {
    const var_pairt &vv = templ.var_pairs[index];
    //    if(k==LOOP || k==OUTL) continue;
    if(v.equs.same_set(vv.first,vv.second)) 
      c.push_back(equal_exprt(vv.first,vv.second));
  }

  for(index_sett::const_iterator it = v.disequs.begin(); it != v.disequs.end(); it++)
  {
    //    if(k==LOOP || k==OUTL) continue;
    const var_pairt &vv = templ.var_pairs[*it];
    c.push_back(notequal_exprt(vv.first,vv.second));
  }
  result = conjunction(c); 
}

/*******************************************************************\

Function: equality_domaint::set_equal

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void equality_domaint::set_equal(
  unsigned index, equ_valuet &value)
{
  assert(index<templ.size());
  const var_pairt &vv = templ.var_pairs[index];
  value.equs.make_union(vv.first,vv.second);
}

/*******************************************************************\

Function: equality_domaint::set_unequal

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void equality_domaint::set_disequal(
  unsigned index, equ_valuet &value)
{
  assert(index<templ.size());
  value.disequs.insert(index);
}

/*******************************************************************\

Function: equality_domaint::get_var_pair

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

const equality_domaint::var_pairt &equality_domaint::get_var_pair(unsigned index)
{
  assert(index<templ.size());
  return templ.var_pairs[index];
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
  const equ_valuet &_v = static_cast<const equ_valuet &>(value);
  equ_valuet v = _v;

  for(unsigned index = 0; index<templ.size(); index++)
  {
    const var_pairt &vv = templ.var_pairs[index];
    if(v.equs.same_set(vv.first,vv.second)) 
    {
      out << from_expr(ns,"",vv.first) << " == " << from_expr(ns,"",vv.second) << std::endl;
    }
  }

  for(index_sett::const_iterator it = v.disequs.begin(); it != v.disequs.end(); it++)
  {
    const var_pairt &vv = templ.var_pairs[*it];
    out << from_expr(ns,"",vv.first) << " != " << from_expr(ns,"",vv.second) << std::endl;
  }
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
  for(unsigned index = 0; index<templ.size(); index++)
  {
    switch(templ.kinds[index])
    {
    case LOOP:
      out << "(LOOP) [ " << from_expr(ns,"",templ.pre_guards[index]) << " | ";
      out << from_expr(ns,"",templ.post_guards[index]) << " ] ===> " << std::endl << "      ";
      break;
    case IN: out << "(IN)   "; break;
    case OUT: case OUTL:
      out << "(OUT)  "; 
      out << from_expr(ns,"",templ.post_guards[index]) << " ===> " << std::endl << "      ";
      break;
    default: assert(false);
    }
    const var_pairt &vv = templ.var_pairs[index];
    out << from_expr(ns,"",vv.first) << " =!= " << from_expr(ns,"",vv.second) << std::endl;
  }
}

/*******************************************************************\

Function: equality_domaint::make_template

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool adapt_types(exprt &v1, exprt &v2)
{
  unsigned size1 = 0, size2 = 0;
  if(v1.type().id()==ID_signedbv) 
    size1 =  to_signedbv_type(v1.type()).get_width();
  if(v1.type().id()==ID_unsignedbv) 
    size1 =  to_unsignedbv_type(v1.type()).get_width();
  if(v2.type().id()==ID_signedbv) 
    size2 =  to_signedbv_type(v2.type()).get_width();
  if(v2.type().id()==ID_unsignedbv) 
    size2 =  to_unsignedbv_type(v2.type()).get_width();
  assert(size1>0); assert(size2>0); //TODO: implement floats

  if(v1.type().id()==v2.type().id())
  {
    if(size1==size2) return true;

    typet new_type = v1.type();
    if(new_type.id()==ID_signedbv) 
      to_signedbv_type(new_type).set_width(std::max(size1,size2));
    else //if(new_type.id()==ID_unsignedbv) 
      to_unsignedbv_type(new_type).set_width(std::max(size1,size2));

    if(size1>size2) v2 = typecast_exprt(v2,new_type);
    else v1 = typecast_exprt(v1,new_type);
    return true;
  }
  
  //types are different
  typet new_type = signedbv_typet(std::max(size1,size2)+1);
  v1 = typecast_exprt(v1,new_type);
  v2 = typecast_exprt(v2,new_type);
  return true;
}

void equality_domaint::make_template(
  const var_listt &vars,
  const guardst &pre_guards,
  const guardst &post_guards,
  const kindst &kinds,
  const namespacet &ns)
{ 
  assert(vars.size() == pre_guards.size());
  assert(vars.size() == post_guards.size());
  assert(vars.size() == kinds.size());
  unsigned size = vars.size(); //just an estimate
  templ.var_pairs.clear(); templ.var_pairs.reserve(size);
  templ.pre_guards.clear(); templ.pre_guards.reserve(size);
  templ.post_guards.clear(); templ.post_guards.reserve(size);
  templ.kinds.clear(); templ.kinds.reserve(size);

  guardst::const_iterator pre_g1 = pre_guards.begin();
  guardst::const_iterator post_g1 = post_guards.begin();
  kindst::const_iterator k1 = kinds.begin();
  for(var_listt::const_iterator v1 = vars.begin(); 
      v1!=vars.end(); v1++, pre_g1++, post_g1++, k1++)
  {
    guardst::const_iterator pre_g2 = pre_g1; pre_g2++;
    guardst::const_iterator post_g2 = post_g1; post_g2++;
    var_listt::const_iterator v2 = v1; v2++;
    kindst::const_iterator k2 = k1; k2++;
    for(;v2!=vars.end(); v2++, pre_g2++, post_g2++, k2++)
    {
      kindt k = domaint::merge_kinds(*k1,*k2);
      if(k==IN) continue;

      symbol_exprt vv1 = *v1;
      symbol_exprt vv2 = *v2;
      if(!adapt_types(vv1,vv2)) continue;

      exprt pre_g = and_exprt(*pre_g1,*pre_g2);
      exprt post_g = and_exprt(*post_g1,*post_g2);
      simplify(pre_g,ns);
      simplify(post_g,ns);

      templ.var_pairs.push_back(var_pairt(vv1,vv2));
      templ.pre_guards.push_back(pre_g);
      templ.post_guards.push_back(post_g);
      templ.kinds.push_back(k);
    }
  }
  assert(templ.var_pairs.size() == templ.pre_guards.size());
  assert(templ.var_pairs.size() == templ.post_guards.size());
  assert(templ.var_pairs.size() == templ.kinds.size());
}

/*******************************************************************\

Function: equality_domaint::get_var_pairs

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void equality_domaint::get_index_set(std::set<unsigned> &indices) 
{
  for(unsigned i=0;i<templ.size(); i++) indices.insert(i);
}
