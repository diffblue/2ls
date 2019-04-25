/*******************************************************************\

Module: Equalities/Disequalities domain

Author: Peter Schrammel

\*******************************************************************/

/// \file
/// Equalities/Disequalities domain

#ifdef DEBUG
#include <iostream>
#include <langapi/languages.h>
#endif

#include <util/find_symbols.h>
#include <util/arith_tools.h>
#include <util/ieee_float.h>
#include <util/simplify_expr.h>

#include "equality_domain.h"
#include "util.h"

void equality_domaint::initialize(valuet &value)
{
  equ_valuet &v=static_cast<equ_valuet &>(value);
  v.equs.clear();
  v.disequs.clear();
}

void equality_domaint::solver_iter_init(valuet &value)
{
  e_it=todo_equs.begin();
  unsatisfiable=false;
}

bool equality_domaint::has_something_to_solve()
{
  if(e_it!=todo_equs.end())
  {
    check_dis=false;
    return true;
  }
  if(todo_disequs.begin()!=todo_disequs.end())
  {
    e_it=todo_disequs.begin();
    check_dis=true;
    return true;
  }
  return false;
}

std::vector<exprt> equality_domaint::get_required_smt_values(size_t row)
{
  std::vector<exprt> r;
  return r;
}

void equality_domaint::set_smt_values(std::vector<exprt> got_values, size_t row)
{
  todo_disequs.insert(*e_it);
}

bool equality_domaint::edit_row(const rowt &row, valuet &inv, bool improved)
{
  if(!check_dis)
    todo_disequs.insert(*e_it);
  return true;
}

void equality_domaint::post_edit()
{
  if(check_dis)
    todo_disequs.erase(e_it);
  else
    todo_equs.erase(e_it);
}

exprt equality_domaint::to_pre_constraints(valuet &_value)
{
  if(check_dis)
    return get_pre_disequ_constraint(*e_it);
  assert(*e_it<templ.size());
  const template_rowt &templ_row=templ[*e_it];
  if(templ_row.kind==OUT || templ_row.kind==OUTL)
    return true_exprt();

  const var_pairt &vv=templ_row.var_pair;
  return implies_exprt(templ_row.pre_guard, equal_exprt(vv.first, vv.second));
}

void equality_domaint::make_not_post_constraints(
  valuet &_value,
  exprt::operandst &cond_exprs)
{
  assert(*e_it<templ.size());
  cond_exprs.resize(1);
  if(check_dis)
  {
    cond_exprs[0]=get_post_not_disequ_constraint(*e_it);
    return;
  }
  const template_rowt &templ_row=templ[*e_it];
  if(templ_row.kind==IN)
  {
    cond_exprs[0]=true_exprt();
    return;
  }

  const var_pairt &vv=templ_row.var_pair;
  exprt c=
    and_exprt(
      templ_row.aux_expr,
      not_exprt(
        implies_exprt(
          templ_row.post_guard,
          equal_exprt(vv.first, vv.second))));
  rename(c);
  cond_exprs[0]=c;
}

exprt equality_domaint::get_pre_equ_constraint(unsigned index)
{
  assert(index<templ.size());
  const template_rowt &templ_row=templ[index];
  if(templ_row.kind==OUT || templ_row.kind==OUTL)
    return true_exprt();

  const var_pairt &vv=templ_row.var_pair;
  return implies_exprt(templ_row.pre_guard, equal_exprt(vv.first, vv.second));
}

exprt equality_domaint::get_post_not_equ_constraint(unsigned index)
{
  assert(index<templ.size());
  const template_rowt &templ_row=templ[index];
  if(templ_row.kind==IN)
    return true_exprt();

  const var_pairt &vv=templ_row.var_pair;
  exprt c=
    and_exprt(
      templ_row.aux_expr,
      not_exprt(
        implies_exprt(
          templ_row.post_guard,
          equal_exprt(vv.first, vv.second))));
  rename(c);
  return c;
}

bool equality_domaint::handle_unsat(valuet &value, bool improved)
{
  equality_domaint::equ_valuet &inv=
    static_cast<equality_domaint::equ_valuet &>(value);
  if(check_dis)
    set_disequal(*e_it, inv);
  unsatisfiable=true;
  return true;
}

exprt equality_domaint::make_permanent(valuet &value)
{
  equality_domaint::equ_valuet &inv=
    static_cast<equality_domaint::equ_valuet &>(value);
  if(unsatisfiable)
  {
    if(!check_dis)
    {
      set_equal(*e_it, inv);

      // due to transitivity, we have to recheck equalities
      //   that did not hold
      todo_equs.insert(todo_disequs.begin(), todo_disequs.end());
      todo_disequs.clear();
    }
    return to_pre_constraints(value);
  }
  return true_exprt();
}

exprt equality_domaint::get_pre_disequ_constraint(unsigned index)
{
  assert(index<templ.size());
  const template_rowt &templ_row=templ[index];
  if(templ_row.kind==OUT || templ_row.kind==OUTL)
    return true_exprt();

  const var_pairt &vv=templ_row.var_pair;
  return
    implies_exprt(templ_row.pre_guard, notequal_exprt(vv.first, vv.second));
}

exprt equality_domaint::get_post_not_disequ_constraint(unsigned index)
{
  assert(index<templ.size());
  const template_rowt &templ_row=templ[index];
  if(templ_row.kind==IN)
    return true_exprt();

  const var_pairt &vv=templ_row.var_pair;
  exprt c=
    and_exprt(
      templ_row.aux_expr,
      not_exprt(
        implies_exprt(
          templ_row.post_guard,
          notequal_exprt(vv.first, vv.second))));
  rename(c);
  return c;
}

void equality_domaint::project_on_vars(
  valuet &value,
  const var_sett &vars,
  exprt &result)
{
#if 0
  if(templ.size()==0)
    return domaint::project_on_vars(value, vars, result);
#endif

  equ_valuet &v=static_cast<equ_valuet &>(value);

  exprt::operandst c;
  for(unsigned index=0; index<templ.size(); index++)
  {
    const var_pairt &vv=templ[index].var_pair;

#if 0
    std::cout << vv.second << std::endl;
#endif
    if(vars.find(vv.first)==vars.end() ||
       (vars.find(vv.second)==vars.end() &&
        !(vv.second.id()==ID_constant &&
          to_constant_expr(vv.second).get_value()=="NULL")))
      continue;

    if(v.equs.same_set(vv.first, vv.second))
    {
      if(templ[index].kind==LOOP)
        c.push_back(
          implies_exprt(
            templ[index].pre_guard,
            equal_exprt(vv.first, vv.second)));
      else
        c.push_back(equal_exprt(vv.first, vv.second));
    }
  }

  for(index_sett::const_iterator it=v.disequs.begin();
      it!=v.disequs.end(); it++)
  {
    const var_pairt &vv=templ[*it].var_pair;

    if(vars.find(vv.first)==vars.end() ||
       (vars.find(vv.second)==vars.end() &&
        !(vv.second.id()==ID_constant &&
          to_constant_expr(vv.second).get_value()=="NULL")))
      continue;

    if(templ[*it].kind==LOOP)
      c.push_back(
        implies_exprt(
          templ[*it].pre_guard,
          notequal_exprt(vv.first, vv.second)));
    else
      c.push_back(notequal_exprt(vv.first, vv.second));
  }
  result=conjunction(c);
}

void equality_domaint::set_equal(
  unsigned index, equ_valuet &value)
{
  assert(index<templ.size());
  const var_pairt &vv=templ[index].var_pair;
  value.equs.make_union(vv.first, vv.second);
}

void equality_domaint::set_disequal(
  unsigned index, equ_valuet &value)
{
  assert(index<templ.size());
  value.disequs.insert(index);
}

const equality_domaint::var_pairt &equality_domaint::get_var_pair(
  unsigned index)
{
  assert(index<templ.size());
  return templ[index].var_pair;
}

void equality_domaint::output_value(
  std::ostream &out,
  const valuet &value,
  const namespacet &ns) const
{
  const equ_valuet &_v=static_cast<const equ_valuet &>(value);
  equ_valuet v=_v;

  for(unsigned index=0; index<templ.size(); index++)
  {
    const var_pairt &vv=templ[index].var_pair;
    if(v.equs.same_set(vv.first, vv.second))
    {
      out << from_expr(ns, "", vv.first) << "=="
          << from_expr(ns, "", vv.second) << std::endl;
    }
  }

  for(index_sett::const_iterator it=v.disequs.begin();
      it!=v.disequs.end(); it++)
  {
    const var_pairt &vv=templ[*it].var_pair;
    out << from_expr(ns, "", vv.first) << "!="
        << from_expr(ns, "", vv.second) << std::endl;
  }
}

void equality_domaint::output_domain(
  std::ostream &out,
  const namespacet &ns) const
{
  for(unsigned index=0; index<templ.size(); index++)
  {
    const template_rowt &templ_row=templ[index];
    switch(templ_row.kind)
    {
    case LOOP:
      out << "(LOOP) [ " << from_expr(ns, "", templ_row.pre_guard) << " | ";
      out << from_expr(ns, "", templ_row.post_guard) << " | ";
      out << from_expr(ns, "", templ_row.aux_expr)
          << " ]===> " << std::endl << "      ";
      break;
    case IN:
      out << "(IN)   ";
      out << from_expr(ns, "", templ_row.pre_guard) << "===> "
          << std::endl << "      ";
      break;
    case OUT: case OUTL:
      out << "(OUT)  ";
      out << from_expr(ns, "", templ_row.post_guard) << "===> "
          << std::endl << "      ";
      break;
    default: assert(false);
    }
    const var_pairt &vv=templ_row.var_pair;
    out << from_expr(ns, "", vv.first) << "=!= "
        << from_expr(ns, "", vv.second) << std::endl;
  }
}

bool equality_domaint::adapt_types(exprt &v1, exprt &v2)
{
  // signed, unsigned integers
  if((v1.type().id()==ID_signedbv || v1.type().id()==ID_unsignedbv) &&
     (v2.type().id()==ID_signedbv || v2.type().id()==ID_unsignedbv))
  {
    unsigned size1=0, size2=0;
    if(v1.type().id()==ID_signedbv)
      size1=to_signedbv_type(v1.type()).get_width();
    if(v1.type().id()==ID_unsignedbv)
      size1=to_unsignedbv_type(v1.type()).get_width();
    if(v2.type().id()==ID_signedbv)
      size2=to_signedbv_type(v2.type()).get_width();
    if(v2.type().id()==ID_unsignedbv)
      size2=to_unsignedbv_type(v2.type()).get_width();

    if(v1.type().id()==v2.type().id())
    {
      if(size1==size2)
        return true;

      typet new_type=v1.type();
      if(new_type.id()==ID_signedbv)
        to_signedbv_type(new_type).set_width(std::max(size1, size2));
      else // if(new_type.id()==ID_unsignedbv)
        to_unsignedbv_type(new_type).set_width(std::max(size1, size2));

      if(size1>size2)
        v2=typecast_exprt(v2, new_type);
      else
        v1=typecast_exprt(v1, new_type);
      return true;
    }

    // types are different
    typet new_type=signedbv_typet(std::max(size1, size2)+1);
    v1=typecast_exprt(v1, new_type);
    v2=typecast_exprt(v2, new_type);
    return true;
  }

  // pointer equality
  if(v1.type().id()==ID_pointer && v2.type().id()==ID_pointer)
  {
    if(to_pointer_type(v1.type()).subtype()==
       to_pointer_type(v2.type()).subtype())
      return true;
    return false;
  }

  if(v1.id()==ID_index || v2.id()==ID_index)
  {
#if 0
    std::cout << "v1: " << v1 << std::endl;
    std::cout << "v2: " << v2 << std::endl;
#endif
    // TODO: implement
    return false;
  }

  return false; // types incompatible
}

void equality_domaint::make_template(
  const var_specst &var_specs,
  const namespacet &ns)
{
  unsigned size=var_specs.size(); // just an estimate
  templ.clear();
  templ.reserve(size);

  for(var_specst::const_iterator v1=var_specs.begin();
      v1!=var_specs.end(); v1++)
  {
    //  NULL pointer checks
    if(v1->var.type().id()==ID_pointer)
    {
      templ.push_back(template_rowt());
      template_rowt &templ_row=templ.back();
      templ_row.var_pair=
        var_pairt(v1->var, null_pointer_exprt(to_pointer_type(v1->var.type())));
      templ_row.pre_guard=v1->pre_guard;
      templ_row.post_guard=v1->post_guard;
      templ_row.aux_expr=v1->aux_expr;
      templ_row.kind=v1->kind;
    }

    var_specst::const_iterator v2=v1; v2++;
    for(; v2!=var_specs.end(); v2++)
    {
      kindt k=domaint::merge_kinds(v1->kind, v2->kind);

#if 0
      // TODO: must be done in caller (for preconditions, e.g.)
      if(k==IN)
        continue;
#endif

      exprt pre_g, post_g, aux_expr;
      merge_and(pre_g, v1->pre_guard, v2->pre_guard, ns);
      merge_and(post_g, v1->post_guard, v2->post_guard, ns);
      merge_and(aux_expr, v1->aux_expr, v2->aux_expr, ns);

      exprt vv1=v1->var;
      exprt vv2=v2->var;
      if(!adapt_types(vv1, vv2))
        continue;

      templ.push_back(template_rowt());
      template_rowt &templ_row=templ.back();
      templ_row.var_pair=var_pairt(vv1, vv2);
      templ_row.pre_guard=pre_g;
      templ_row.post_guard=post_g;
      templ_row.aux_expr=aux_expr;
      templ_row.kind=k;
    }
  }
}

const exprt equality_domaint::initialize_solver(
  const local_SSAt &SSA,
  const exprt &precondition,
  template_generator_baset &template_generator)
{
  get_index_set(todo_equs);
  return true_exprt();
}

void equality_domaint::get_index_set(std::set<unsigned> &indices)
{
  for(unsigned i=0; i<templ.size(); i++)
    indices.insert(i);
}
