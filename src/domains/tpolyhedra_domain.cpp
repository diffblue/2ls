#include "tpolyhedra_domain.h"
#include "util.h"

#include <iostream>

#include <util/find_symbols.h>
#include <util/i2string.h>
#include <util/simplify_expr.h>
#include <langapi/languages.h>

#define SYMB_BOUND_VAR "symb_bound#"

//#define ENABLE_HEURISTICS

/*******************************************************************\

Function: tpolyhedra_domaint::initialize

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void tpolyhedra_domaint::initialize(valuet &value)
{
#if 0
  if(templ.size()==0) return domaint::initialize(value);
#endif

  templ_valuet &v = static_cast<templ_valuet&>(value);
  v.resize(templ.size());
  for(unsigned row = 0; row<templ.size(); row++)
  {
    if(templ[row].kind==IN) v[row] = true_exprt(); //marker for oo
    else v[row] = false_exprt(); //marker for -oo
  }
}

/*******************************************************************\

Function: tpolyhedra_domaint::join

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void tpolyhedra_domaint::join(valuet &value1, const valuet &value2)
{
#if 0
  if(templ.size()==0) return domaint::join(value1,value2);
#endif

  templ_valuet &v1 = static_cast<templ_valuet&>(value1);
  const templ_valuet &v2 = static_cast<const templ_valuet&>(value2);
  assert(v1.size()==templ.size());
  assert(v1.size()==v2.size());
  for(unsigned row = 0; row<templ.size(); row++)
  {
    if(is_row_value_inf(v1[row]) || is_row_value_inf(v2[row])) 
      v1[row] = true_exprt();
    else if(is_row_value_neginf(v1[row])) v1[row] = v2[row];
    else if(!is_row_value_neginf(v2[row])) 
    {
      if(less_than(v1[row],v2[row])) v1[row] = v2[row];
    }
  }
}

/*******************************************************************\

Function: tpolyhedra_domaint::between

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

tpolyhedra_domaint::row_valuet tpolyhedra_domaint::between(
  const row_valuet &lower, const row_valuet &upper)
{
  if(lower.type().id()==upper.type().id() && 
     (lower.type().id()==ID_signedbv || lower.type().id()==ID_unsignedbv))
  {
    typet type = lower.type();
    mp_integer vlower, vupper;
    to_integer(lower, vlower);
    to_integer(upper, vupper);
    assert(vupper>=vlower);
    if(vlower+1==vupper) return from_integer(vlower,lower.type()); //floor

#ifdef ENABLE_HEURISTICS
    //heuristics
    if(type.id()==ID_unsignedbv)
    {
      mp_integer vlargest = to_unsignedbv_type(type).largest();
      if(vlower==mp_integer(0) && vupper==vlargest)
        return from_integer(mp_integer(1),type);
      if(vlower==mp_integer(1) && vupper==vlargest)
        return from_integer(mp_integer(vupper-1),type);
      if(vlower==mp_integer(1) && vupper==vlargest-1)
        return from_integer(mp_integer(2),type);
      if(vlower<mp_integer(128) && vupper==vlargest)
        return from_integer(vlargest-1,type);
      if(vlower<mp_integer(128) && vupper==vlargest-1)
        return from_integer(mp_integer(255),type); 
    }
    if(type.id()==ID_signedbv)
    { 
      mp_integer vlargest = to_signedbv_type(type).largest();
      if(vlower==-vlargest && vupper==vlargest)
        return from_integer(mp_integer(0),type);
      if(vlower==mp_integer(1) && vupper==vlargest)
        return from_integer(mp_integer(2),type);
      if(vlower==mp_integer(-1) && vupper==vlargest)
        return from_integer(mp_integer(0),type);
      if(vlower==mp_integer(0) &&  vupper==vlargest)
        return from_integer(mp_integer(vupper-1),type);
      if(vlower==-(vlargest/2) && vupper==vlargest)
        return from_integer(mp_integer(vlargest/2+1),type);
      if(vlower==vlargest/2+1 && vupper==vlargest)
        return from_integer(mp_integer(vlargest/2+2),type);
      if(vlower==mp_integer(0) && vupper==vlargest-1)
        return from_integer(mp_integer(1),type);
      if(vlower<mp_integer(128) && vupper==vlargest)
        return from_integer(vlargest-1,type);
      if(vlower<mp_integer(128) && vupper==vlargest-1)
        return from_integer(mp_integer(255),type);
      if(vlower<mp_integer(-128) && vupper==mp_integer(255))
      return from_integer(mp_integer(-255),type); 
    }
#endif

    return from_integer((vupper+vlower)/2,type);
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
      ieee_floatt res(to_floatbv_type(lower.type()));
      res.unpack((plower+pupper)/2); //...by computing integer mean
      return res.to_expr();
    }
    ieee_floatt res(to_floatbv_type(lower.type()));
    res.make_zero();
    return res.to_expr();
  }
  assert(false); //types do not match or are not supported
}

/*******************************************************************\

Function: tpolyhedra_domaint::less_than

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool tpolyhedra_domaint::less_than(const row_valuet &v1, const row_valuet &v2)
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

Function: tpolyhedra_domaint::get_row_pre_constraint

  Inputs:

 Outputs:

 Purpose: pre_guard ==> row_expr <= row_value

\*******************************************************************/

exprt tpolyhedra_domaint::get_row_constraint(const rowt &row, 
  const row_valuet &row_value)
{
  assert(row<templ.size());
  kindt k = templ[row].kind;
  if(k==OUT || k==OUTL) return true_exprt();
  if(is_row_value_neginf(row_value)) return false_exprt();
  if(is_row_value_inf(row_value)) return true_exprt();
  return binary_relation_exprt(templ[row].expr,ID_le,row_value);
}

exprt tpolyhedra_domaint::get_row_pre_constraint(const rowt &row, 
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


exprt tpolyhedra_domaint::get_row_pre_constraint(const rowt &row, 
  const templ_valuet &value)
{
  assert(value.size()==templ.size());
  return get_row_pre_constraint(row,value[row]);
}

/*******************************************************************\

Function: tpolyhedra_domaint::get_row_post_constraint

  Inputs:

 Outputs:

 Purpose: row_expr <= row_value

\*******************************************************************/

exprt tpolyhedra_domaint::get_row_post_constraint(const rowt &row, 
  const row_valuet &row_value)
{
  assert(row<templ.size());
  const template_rowt &templ_row = templ[row];
  if(templ_row.kind==IN) return true_exprt();

#if 0 //TEST for disjunctive domains
  if(templ.size()==4)
  {
  exprt guard = true_exprt();
  if(row==1 || row==3) 
    return guard = 
      binary_relation_exprt(templ_row.expr,ID_gt,from_integer(mp_integer(0),templ_row.expr.type()));
  else
    return guard =
      binary_relation_exprt(templ_row.expr,ID_lt,from_integer(mp_integer(0),templ_row.expr.type()));
  if(is_row_value_neginf(row_value)) 
    return implies_exprt(templ_row.post_guard, implies_exprt(guard,false_exprt()));
  if(is_row_value_inf(row_value)) 
    return implies_exprt(templ_row.post_guard, implies_exprt(guard,true_exprt()));
  exprt c = implies_exprt(templ_row.post_guard, 
			  implies_exprt(guard,binary_relation_exprt(templ_row.expr,ID_le,row_value)));
  }
#endif

  if(is_row_value_neginf(row_value)) 
    return implies_exprt(templ_row.post_guard,false_exprt());
  if(is_row_value_inf(row_value)) 
    return implies_exprt(templ_row.post_guard,true_exprt());
  exprt c = implies_exprt(templ_row.post_guard, 
	    binary_relation_exprt(templ_row.expr,ID_le,row_value));
  if(templ_row.kind==LOOP) rename(c);
  return c;
}

exprt tpolyhedra_domaint::get_row_post_constraint(const rowt &row, 
  const templ_valuet &value)
{
  assert(value.size()==templ.size());
  return get_row_post_constraint(row,value[row]);
}

/*******************************************************************\

Function: tpolyhedra_domaint::to_pre_constraints

  Inputs:

 Outputs:

 Purpose: /\_all_rows ( pre_guard ==> (row_expr <= row_value) )

\*******************************************************************/

exprt tpolyhedra_domaint::to_pre_constraints(const templ_valuet &value)
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

Function: tpolyhedra_domaint::make_not_post_constraints

  Inputs:

 Outputs:

 Purpose: for all rows !(post_guard ==> (row_expr <= row_value))
          to be connected disjunctively

\*******************************************************************/

void tpolyhedra_domaint::make_not_post_constraints(const templ_valuet &value,
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
    rename(value_exprs[row]);
    cond_exprs[row] = 
      and_exprt(templ[row].aux_expr,
		not_exprt(get_row_post_constraint(row,value)));
  }
}

/*******************************************************************\

Function: tpolyhedra_domaint::get_row_symb_value

  Inputs:

 Outputs:

 Purpose: generates symbolic value symbol

\*******************************************************************/

symbol_exprt tpolyhedra_domaint::get_row_symb_value(const rowt &row)
{
  assert(row<templ.size());
  return symbol_exprt(SYMB_BOUND_VAR+i2string(domain_number)+"$"+
		      i2string(row),templ[row].expr.type());
}

/*******************************************************************\

Function: tpolyhedra_domaint::get_row_symb_pre_constraint

  Inputs:

 Outputs:

 Purpose: pre_guard ==> (row_expr <= symb_value)

\*******************************************************************/

exprt tpolyhedra_domaint::get_row_symb_pre_constraint(const rowt &row, 
				    const row_valuet &row_value)
{
  assert(row<templ.size());
  const template_rowt &templ_row = templ[row];
  if(templ_row.kind==OUT || templ_row.kind==OUTL) return true_exprt();
  return implies_exprt(templ_row.pre_guard,  //REMARK: and_expr ==> loop15 regression
    binary_relation_exprt(templ_row.expr,ID_le,get_row_symb_value(row)));
}

/*******************************************************************\

Function: tpolyhedra_domaint::get_row_symb_post_constraint

  Inputs:

 Outputs:

 Purpose: post_guard && (row_expr >= row_symb_value)  (!!!)

\*******************************************************************/

exprt tpolyhedra_domaint::get_row_symb_post_constraint(const rowt &row)
{
  assert(row<templ.size());
  const template_rowt &templ_row = templ[row];
  if(templ_row.kind==IN) return true_exprt();
  exprt c = and_exprt(templ_row.post_guard,
    binary_relation_exprt(templ_row.expr,ID_ge,get_row_symb_value(row)));
  rename(c);
  return and_exprt(templ_row.aux_expr,c);
}


/*******************************************************************\

Function: tpolyhedra_domaint::to_symb_pre_constraints

  Inputs:

 Outputs:

 Purpose: pre_guard ==> (row_expr <= symb_row_value)

\*******************************************************************/

exprt tpolyhedra_domaint::to_symb_pre_constraints(const templ_valuet &value)
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

Function: tpolyhedra_domaint::to_symb_pre_constraints

  Inputs:

 Outputs:

 Purpose: pre_guard ==> (row_expr <= symb_row_value)

\*******************************************************************/

exprt tpolyhedra_domaint::to_symb_pre_constraints(const templ_valuet &value,
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

Function: tpolyhedra_domaint::to_symb_post_constraints

  Inputs:

 Outputs:

 Purpose: /\_i post_guard ==> (row_expr >= symb_row_value)

\*******************************************************************/

exprt tpolyhedra_domaint::to_symb_post_constraints(
   const std::set<rowt> &symb_rows)
{
  exprt::operandst c; 
  for(std::set<rowt>::const_iterator it = symb_rows.begin(); 
      it != symb_rows.end(); it++)
  {
    c.push_back(get_row_symb_post_constraint(*it));
  }
  return conjunction(c); 
}

/*******************************************************************\

Function: tpolyhedra_domaint::get_row_symb_value_constraint

  Inputs:

 Outputs:

 Purpose: row_value_value <= symb_row

\*******************************************************************/

exprt tpolyhedra_domaint::get_row_symb_value_constraint(const rowt &row, 
			    	const row_valuet &row_value, bool geq)
{
  if(is_row_value_neginf(row_value)) return false_exprt();
  if(is_row_value_inf(row_value)) return true_exprt();
  exprt c = binary_relation_exprt(get_row_symb_value(row),
				  geq ? ID_ge : ID_le,row_value);
  return c;
}


/*******************************************************************\

Function: tpolyhedra_domaint::get_row_value

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

tpolyhedra_domaint::row_valuet tpolyhedra_domaint::get_row_value(
  const rowt &row, const templ_valuet &value)
{
  assert(row<value.size());
  assert(value.size()==templ.size());
  return value[row];
}

/*******************************************************************\

Function: tpolyhedra_domaint::project_on_vars

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void tpolyhedra_domaint::project_on_vars(valuet &value, 
				       const var_sett &vars, exprt &result)
{
#if 0
  if(templ.size()==0) return domaint::project_on_vars(value,vars,result);
#endif

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
      if(is_row_value_neginf(row_v)) 
	c.push_back(implies_exprt(templ_row.pre_guard,false_exprt()));
      else if(is_row_value_inf(row_v)) 
	c.push_back(implies_exprt(templ_row.pre_guard,true_exprt()));
      else c.push_back(implies_exprt(templ_row.pre_guard,
		       binary_relation_exprt(templ_row.expr,ID_le,row_v)));
    }
    else
    {
      if(is_row_value_neginf(row_v)) 
	c.push_back(false_exprt());
      else if(is_row_value_inf(row_v)) 
	c.push_back(true_exprt());
      else c.push_back(binary_relation_exprt(templ_row.expr,ID_le,row_v));
    }
  }
  result = conjunction(c);
}

/*******************************************************************\

Function: tpolyhedra_domaint::set_row_value

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void tpolyhedra_domaint::set_row_value(
  const rowt &row, const tpolyhedra_domaint::row_valuet &row_value, templ_valuet &value)
{
  assert(row<value.size());
  assert(value.size()==templ.size());
  value[row] = row_value;
}


/*******************************************************************\

Function: tpolyhedra_domaint::get_row_max_value

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

tpolyhedra_domaint::row_valuet tpolyhedra_domaint::get_max_row_value(
  const tpolyhedra_domaint::rowt &row)
{
  const template_rowt &templ_row = templ[row];
  return get_max_value(templ_row.expr);
}

tpolyhedra_domaint::row_valuet tpolyhedra_domaint::get_max_value(
  const row_exprt &expr)
{
  if(expr.type().id()==ID_signedbv)
  {
    return to_signedbv_type(expr.type()).largest_expr();
  }
  if(expr.type().id()==ID_unsignedbv)
  {
    return to_unsignedbv_type(expr.type()).largest_expr();
  }
  if(expr.type().id()==ID_floatbv) 
  {
    ieee_floatt max(to_floatbv_type(expr.type()));
    max.make_fltmax();
    return max.to_expr();
  }
  assert(false); //type not supported
}

/*******************************************************************\

Function: tpolyhedra_domaint::get_row_max_value

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

tpolyhedra_domaint::row_valuet tpolyhedra_domaint::get_min_row_value(
  const tpolyhedra_domaint::rowt &row)
{
  const template_rowt &templ_row = templ[row];
  return get_min_value(templ_row.expr);
}

tpolyhedra_domaint::row_valuet tpolyhedra_domaint::get_min_value(
  const row_exprt &expr)
{
  if(expr.type().id()==ID_signedbv)
  {
    return to_signedbv_type(expr.type()).smallest_expr();
  }
  if(expr.type().id()==ID_unsignedbv)
  {
    return to_unsignedbv_type(expr.type()).smallest_expr();
  }
  if(expr.type().id()==ID_floatbv) 
  {
    ieee_floatt min(to_floatbv_type(expr.type()));
    min.make_fltmin();
    return min.to_expr();
  }
  assert(false); //type not supported
}

/*******************************************************************\

Function: tpolyhedra_domaint::output_value

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void tpolyhedra_domaint::output_value(std::ostream &out, const valuet &value, 
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
    out << "( " << from_expr(ns,"",templ_row.expr) << " <= ";
    if(is_row_value_neginf(v[row])) out << "-oo";
    else if(is_row_value_inf(v[row])) out << "oo";
    else out << from_expr(ns,"",v[row]);
    out << " )" << std::endl;
  }
}

/*******************************************************************\

Function: tpolyhedra_domaint::output_domain

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void tpolyhedra_domaint::output_domain(std::ostream &out, const namespacet &ns) const
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
        from_expr(ns,"",templ_row.expr) << " <= CONST )" << std::endl;
  }
}

/*******************************************************************\

Function: tpolyhedra_domaint::template_size

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

unsigned tpolyhedra_domaint::template_size()
{
  return templ.size();
}

/*******************************************************************\

Function: tpolyhedra_domaint::is_row_value_neginf

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool tpolyhedra_domaint::is_row_value_neginf(const row_valuet & row_value) const
{
  return row_value.get(ID_value)==ID_false;
}

/*******************************************************************\

Function: tpolyhedra_domaint::is_row_value_inf

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool tpolyhedra_domaint::is_row_value_inf(const row_valuet & row_value) const
{
  return row_value.get(ID_value)==ID_true;
}

/*******************************************************************\

Function: tpolyhedra_domaint::rename_for_row

  Inputs:

 Outputs:

 Purpose: add row suffix to non-symbolic-bound variables in expression 
          (required for strategy iteration (binsearch3))

\*******************************************************************/


void tpolyhedra_domaint::rename_for_row(exprt &expr, const rowt &row)
{
  if(row==0) return; //do not rename
  if(expr.id()==ID_symbol || expr.id()==ID_nondet_symbol)
  {
    const std::string &old_id = expr.get_string(ID_identifier);
    if(old_id.find(SYMB_BOUND_VAR)==std::string::npos) 
    {
      irep_idt id = old_id + "_" + i2string(row);
      expr.set(ID_identifier,id);
    }
  }
  for(unsigned i=0; i< expr.operands().size(); i++)
    rename_for_row(expr.operands()[i],row);
}

/*******************************************************************\

Function: add_template_row

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

tpolyhedra_domaint::template_rowt &tpolyhedra_domaint::add_template_row(
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
  extend_expr_types(templ_row.expr);
  templ_row.pre_guard = pre_guard;
  templ_row.post_guard = post_guard;
  templ_row.aux_expr = aux_expr;
  templ_row.kind = kind;
  return templ_row;
}

/*******************************************************************\

Function: add_interval_template

  Inputs:

 Outputs:

 Purpose: +-x<=c

\*******************************************************************/

void tpolyhedra_domaint::add_interval_template(const var_specst &var_specs,
					     const namespacet &ns)
{
  unsigned size = 2*var_specs.size();
  templ.reserve(templ.size()+size);
  
  for(var_specst::const_iterator v = var_specs.begin(); 
      v!=var_specs.end(); v++)
  {
    if(v->kind==IN) continue; 

    // x
    add_template_row(v->var,v->pre_guard,v->post_guard,
		     v->aux_expr, v->kind);

    // -x
    add_template_row(unary_minus_exprt(v->var,v->var.type()),
		     v->pre_guard,v->post_guard,v->aux_expr, v->kind);
  }
}

/*******************************************************************\

Function: add_difference_template

  Inputs:

 Outputs:

 Purpose: x+-y<=c

\*******************************************************************/

void tpolyhedra_domaint::add_difference_template(const var_specst &var_specs,
					 const namespacet &ns)
{ 
  unsigned size = var_specs.size()*(var_specs.size()-1);
  templ.reserve(templ.size()+size);
  
  for(var_specst::const_iterator v1 = var_specs.begin(); 
      v1!=var_specs.end(); v1++)
  {
    var_specst::const_iterator v2 = v1; v2++;
    for(; v2!=var_specs.end(); v2++)
    {
      kindt k = domaint::merge_kinds(v1->kind,v2->kind);
      if(k==IN) continue; 
      if(k==LOOP && v1->pre_guard!=v2->pre_guard) continue; //TEST: we need better heuristics

      exprt pre_g, post_g, aux_expr;
      merge_and(pre_g, v1->pre_guard, v2->pre_guard, ns);
      merge_and(post_g, v1->post_guard, v2->post_guard, ns);
      merge_and(aux_expr, v1->aux_expr, v2->aux_expr, ns);

      // x1 - x2
      add_template_row(minus_exprt(v1->var,v2->var),pre_g,post_g,aux_expr,k);

      // x2 - x1
      add_template_row(minus_exprt(v2->var,v1->var),pre_g,post_g,aux_expr,k);
    }
  }
}

/*******************************************************************\

Function: add_quadratic_template

  Inputs:

 Outputs:

 Purpose: +-x^2<=c

\*******************************************************************/

void tpolyhedra_domaint::add_quadratic_template(const var_specst &var_specs,
					 const namespacet &ns)
{ 
  unsigned size = 2*var_specs.size();
  templ.reserve(templ.size()+size);
  
  for(var_specst::const_iterator v = var_specs.begin(); 
      v!=var_specs.end(); v++)
  {
    if(v->kind==IN) continue; 

    // x
    add_template_row(mult_exprt(v->var,v->var),
		     v->pre_guard,v->post_guard,v->aux_expr,v->kind);

    // -x
    add_template_row(unary_minus_exprt(mult_exprt(v->var,v->var),v->var.type()),
		     v->pre_guard,v->post_guard,v->aux_expr,v->kind);
  }}

/*******************************************************************\

Function: add_sum_template

  Inputs:

 Outputs:

 Purpose: x+y<=c, -x-y<=c

\*******************************************************************/

void tpolyhedra_domaint::add_sum_template(const var_specst &var_specs,
					    const namespacet &ns)
{
  unsigned size = var_specs.size()*(var_specs.size()-1);
  templ.reserve(templ.size()+size);
  
  for(var_specst::const_iterator v1 = var_specs.begin(); 
      v1!=var_specs.end(); v1++)
  {
    var_specst::const_iterator v2 = v1; v2++;
    for(; v2!=var_specs.end(); v2++)
    {
      kindt k = domaint::merge_kinds(v1->kind,v2->kind);
      if(k==IN) continue; 
      if(k==LOOP && v1->pre_guard!=v2->pre_guard) continue; //TEST: we need better heuristics

      exprt pre_g, post_g, aux_expr;
      merge_and(pre_g, v1->pre_guard, v2->pre_guard, ns);
      merge_and(post_g, v1->post_guard, v2->post_guard, ns);
      merge_and(aux_expr, v1->aux_expr, v2->aux_expr, ns);

      // x1 + x2
      add_template_row(plus_exprt(v1->var,v2->var),pre_g,post_g,aux_expr,k);

      // -x1 - x2
      add_template_row(minus_exprt(
			 unary_minus_exprt(v1->var,v1->var.type()),v2->var),
		       pre_g,post_g,aux_expr,k);
    }
  }

}

/*******************************************************************\

Function: tpolyhedra_domaint::positive_template()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void tpolyhedra_domaint::positive_template(std::vector<exprt> &templates)
{
   templates.reserve(templ.size()/2);
   for(int i=0;i<templates.size();++i)
   {
     templates[i] = templ[2*i].expr;
   } 
}
