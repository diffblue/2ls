/*******************************************************************\

Module: Abstract domain for representing heap

Author: Viktor Malik

\*******************************************************************/

/// \file
/// Abstract domain for representing heap

#include "heap_domain.h"
#include <algorithm>
#include <ssa/address_canonizer.h>

/// Initialize abstract value. Clears value with empty value rows corresponding
/// to template.
void heap_domaint::initialize(domaint::valuet &value)
{
  heap_valuet &val=static_cast<heap_valuet &>(value);
  for(int i=0; i<templ.size(); i++)
    val.emplace_back(row_valuet(ns));
}

/// Create domain template for given set of variables. Template contains a row
/// for each pointer-typed variable and  field of a dynamic object.
void heap_domaint::make_template(
  const domaint::var_specst &var_specs,
  const namespacet &ns)
{
  unsigned long size=var_specs.size();
  templ.clear();
  templ.reserve(size);

  for(const var_spect &v : var_specs)
  {
    if(v.kind==IN)
      continue;

    // Create template for each pointer
    const vart &var=v.var;
    if(var.type().id()==ID_pointer)
    {
      const typet &pointed_type=ns.follow(var.type().subtype());
      add_template_row(v, pointed_type);

      if(var.id()==ID_symbol &&
         id2string(to_symbol_expr(var).get_identifier()).find(
           "__CPROVER_deallocated")!=std::string::npos)
      {
        for(const var_spect &v_other : var_specs)
        {
          if(!(v_other.var.type().id()==ID_pointer && v_other.kind==LOOP &&
               v_other.pre_guard==v.pre_guard))
          {
            continue;
          }

          if(v_other.var.id()==ID_symbol &&
             id2string(to_symbol_expr(v_other.var).get_identifier()).find(
               "__CPROVER_")!=std::string::npos)
          {
            continue;
          }

          add_template_row_pair(v, v_other, pointed_type);
        }
      }
    }
  }
}

std::vector<exprt> heap_domaint::get_required_smt_values(size_t row)
{
  std::vector<exprt> r;
  if(strategy_value_exprs[row].id()==ID_and)
  {
    r.push_back(strategy_value_exprs[row].op0());
    r.push_back(strategy_value_exprs[row].op1());
  }
  else
  {
    r.push_back(strategy_value_exprs[row]);
  }
  return r;
}

void heap_domaint::set_smt_values(std::vector<exprt> got_values, size_t row)
{
  solver_value_op0=got_values[0];
  if(strategy_value_exprs[row].id()==ID_and)
  {
    solver_value_op1=got_values[1];
  }
}


/// Add a template row.
/// \param var_spec: Variable specification
/// \param pointed_type: Pointed type
void heap_domaint::add_template_row(
  const var_spect &var_spec,
  const typet &pointed_type)
{
  const vart &var=var_spec.var;

  templ.push_back(template_rowt());
  template_rowt &templ_row=templ.back();
  templ_row.expr=var;
  templ_row.pre_guard=var_spec.pre_guard;
  templ_row.post_guard=var_spec.post_guard;
  templ_row.aux_expr=var_spec.aux_expr;
  templ_row.kind=var_spec.kind;
}

/// Add a template row with a pair of variables as expression.
/// \param var_spec1: First variable specification
/// \param var_spec2: Second variable specification
/// \param pointed_type: Pointed type
void heap_domaint::add_template_row_pair(
  const domaint::var_spect &var_spec1,
  const domaint::var_spect &var_spec2,
  const typet &pointed_type)
{
  const exprt var_pair=and_exprt(var_spec1.var, var_spec2.var);

  templ.push_back(template_rowt());
  template_rowt &templ_row=templ.back();
  templ_row.expr=var_pair;
  templ_row.pre_guard=var_spec1.pre_guard;
  templ_row.post_guard=var_spec1.post_guard;
  templ_row.aux_expr=var_spec1.aux_expr;
  templ_row.kind=var_spec1.kind;
}

/// Create entry constraints as a conjuction of entry expressions for each
/// template row.
/// \return Entry constraints expression for a value.
exprt heap_domaint::to_pre_constraints(valuet &_value)
{
  heap_domaint::heap_valuet &value=
    static_cast<heap_domaint::heap_valuet &>(_value);
  assert(value.size()==templ.size());
  exprt::operandst c;
  for(rowt row=0; row<templ.size(); ++row)
  {
    c.push_back(get_row_pre_constraint(row, value[row]));
  }
  return conjunction(c);
}

/// Create exit constraints for each value row. Each expression is a negation of
/// a row expression (for solving the "exists forall" problem).
/// \return Exit constraint expression for each row.
void heap_domaint::make_not_post_constraints(
  valuet &_value,
  exprt::operandst &cond_exprs)
{
  heap_domaint::heap_valuet &value=
    static_cast<heap_domaint::heap_valuet &>(_value);
  assert(value.size()==templ.size());
  cond_exprs.resize(templ.size());
  strategy_value_exprs.resize(templ.size());

  for(rowt row=0; row<templ.size(); ++row)
  {
    strategy_value_exprs[row]=templ[row].expr;
    rename(strategy_value_exprs[row]);
    const exprt row_expr=not_exprt(get_row_post_constraint(row, value[row]));
    cond_exprs[row]=and_exprt(templ[row].aux_expr, row_expr);
  }
}

/// Create entry constraint expression for a row.
/// \return Exit constraint expression for each row.
exprt heap_domaint::get_row_pre_constraint(
  const rowt &row,
  const row_valuet &row_value) const
{
  assert(row<templ.size());
  const template_rowt &templ_row=templ[row];
  kindt k=templ_row.kind;
  // For exit variables the result is true
  if(k==OUT || k==OUTL)
    return true_exprt();

  const exprt row_expr=row_value.get_row_expr(templ_row.expr);
  return implies_exprt(templ_row.pre_guard, row_expr);
}

/// Create exit constraint expression for a row.
/// \return Exit constraint expression for each row.
exprt heap_domaint::get_row_post_constraint(
  const rowt &row,
  const row_valuet &row_value)
{
  assert(row<templ.size());
  const template_rowt &templ_row=templ[row];
  // For entry variables the result is true
  if(templ_row.kind==IN)
    return true_exprt();

  const exprt row_expr=
    row_value.get_row_expr(templ_row.expr);
  exprt c=implies_exprt(templ_row.post_guard, row_expr);
  if(templ_row.kind==LOOP)
    rename(c);
  return c;
}

void heap_domaint::output_value(
  std::ostream &out,
  const domaint::valuet &value,
  const namespacet &ns) const
{
  const heap_valuet &val=static_cast<const heap_valuet &>(value);
  for(rowt row=0; row<templ.size(); ++row)
  {
    const template_rowt &templ_row=templ[row];
    switch(templ_row.kind)
    {
    case LOOP:
      out << "(LOOP) [ " << from_expr(ns, "", templ_row.pre_guard) << " | ";
      out << from_expr(ns, "", templ_row.post_guard) << " | ";
      out << from_expr(ns, "", templ_row.aux_expr) << " ] ===> " << std::endl
          << "       ";
      break;
    case IN:
      out << "(IN)   ";
      break;
    case OUT:
    case OUTL:
      out << "(OUT)  ";
      break;
    default:
      assert(false);
    }
    out << "( " << from_expr(ns, "", templ_row.expr) << " == "
        << from_expr(ns, "", val[row].get_row_expr(templ_row.expr))
        << " )"
        << std::endl;
  }
}

void heap_domaint::output_domain(std::ostream &out, const namespacet &ns) const
{
  for(unsigned i=0; i<templ.size(); ++i)
  {
    const template_rowt &templ_row=templ[i];
    switch(templ_row.kind)
    {
    case LOOP:
      out << "(LOOP) [ " << from_expr(ns, "", templ_row.pre_guard) << " | ";
      out << from_expr(ns, "", templ_row.post_guard) << " | ";
      out << from_expr(ns, "", templ_row.aux_expr)
          << " ] ===> " << std::endl << "      ";
      break;
    case IN:
      out << "(IN)   ";
      out << from_expr(ns, "", templ_row.pre_guard) << " ===> "
          << std::endl << "      ";
      break;
    case OUT:
    case OUTL:
      out << "(OUT)  ";
      out << from_expr(ns, "", templ_row.post_guard) << " ===> "
          << std::endl << "      ";
      break;
    default:
      assert(false);
    }

    out << i << ": " << from_expr(ns, "", templ_row.expr)
        << "--points_to--> Locations" << std::endl;
  }
}

void heap_domaint::project_on_vars(
  domaint::valuet &value,
  const domaint::var_sett &vars,
  exprt &result)
{
  const heap_valuet &val=static_cast<heap_valuet &>(value);
  assert(val.size()==templ.size());

  exprt::operandst c;
  for(rowt row=0; row<templ.size(); ++row)
  {
    const template_rowt &templ_row=templ[row];

    if(!vars.empty())
    {
      if(templ_row.expr.id()==ID_and)
      {
        if(vars.find(templ_row.expr.op0())==vars.end() &&
           vars.find(templ_row.expr.op1())==vars.end())
          continue;
      }
      else if(vars.find(templ_row.expr)==vars.end())
        continue;
    }

    const row_valuet &row_val=val[row];
    if(templ_row.kind==LOOP)
    {
      const exprt row_expr=row_val.get_row_expr(templ_row.expr);
      c.push_back(implies_exprt(templ_row.pre_guard, row_expr));
    }
    else
    {
      exprt row_expr=row_val.get_row_expr(templ_row.expr);
      c.push_back(row_expr);
    }
  }
  result=conjunction(c);
}

/// Converts a constant returned from the solver to the corresponding
/// expression.
exprt heap_domaint::value_to_ptr_exprt(const exprt &expr)
{
  if(expr.id()==ID_constant)
  {
    const std::string value=id2string(to_constant_expr(expr).get_value());
    if(value.substr(value.size()/2).find_first_not_of('0')!=std::string::npos)
      return plus_exprt(expr.op0(), constant_exprt::integer_constant(0));
    else
      return expr.op0();
  }

  return expr;
}

/// Not used.
void heap_domaint::join(domaint::valuet &value1, const domaint::valuet &value2)
{
  heap_valuet &val1=static_cast<heap_valuet &>(value1);
  const heap_valuet &val2=static_cast<const heap_valuet &>(value2);
  assert(val1.size()==templ.size());
  assert(val2.size()==val1.size());
}

/// Get location number of a given symbol.
/// \param expr: Symbol expression.
/// \return Number of location, or -1 if symbol is input.
int heap_domaint::get_symbol_loc(const exprt &expr)
{
  assert(expr.id()==ID_symbol);
  std::string expr_id=id2string(to_symbol_expr(expr).get_identifier());
  if(expr_id.find('#')==std::string::npos)
    return -1;
  std::string loc_str=expr_id.substr(expr_id.find_last_not_of("0123456789")+1);
  assert(!loc_str.empty());
  return std::stoi(loc_str);
}

/// \param ptr_expr: Pointer expression (variable)
/// \param ptr_value: Value (object or address) of the pointer
/// \return Equality between pointer and its value with correct types
const exprt ptr_equality(
  const exprt &ptr_expr,
  const exprt &ptr_value,
  const namespacet &ns)
{
  exprt value;
  if(ptr_expr.type()==ptr_value.type())
    value=ptr_value;
  else if(ns.follow(ptr_expr.type().subtype())==ns.follow(ptr_value.type()))
    value=address_of_exprt(ptr_value);
  else
  {
    value=typecast_exprt(
      address_of_exprt(ptr_value),
      ns.follow(ptr_expr.type()));
  }
  return equal_exprt(ptr_expr, value);
}

/// Row value is a disjuction of equalities between templ_expr and addresses of
/// dynamic objects from the points_to set.
/// \param templ_expr: Template expression
/// \param rename_templ_expr: Unused
/// \return Formula corresponding to the template row
exprt heap_domaint::row_valuet::get_row_expr(const vart &templ_expr) const
{
  if(nondet)
    return true_exprt();
  if(points_to.empty())
    return false_exprt();

  // Points to expression
  exprt::operandst result;
  for(const exprt &pt : points_to)
  {
    if(templ_expr.id()==ID_and)
    {
      result.push_back(
        and_exprt(
          ptr_equality(templ_expr.op0(), pt.op0(), ns),
          ptr_equality(templ_expr.op1(), pt.op1(), ns)));
    }
    else
      result.push_back(ptr_equality(templ_expr, pt, ns));
  }
  return disjunction(result);
}

/// Add new expression to the set of pointed objects.
/// In case it is already there, set row to nondet.
bool heap_domaint::row_valuet::add_points_to(const exprt &expr)
{
  if(points_to.find(expr)==points_to.end())
    points_to.insert(expr);
  else
    nondet=true;
  return true;
}

bool heap_domaint::row_valuet::set_nondet()
{
  bool changed=!nondet;
  nondet=true;
  return changed;
}

/// Clear the points to set and set nondet to false
void heap_domaint::row_valuet::clear()
{
  nondet=false;
  points_to.clear();
}

/// Restrict template to a given symbolic path. For each template row, we add
/// all other loop guards in their positive or negative form (as specified by
/// path) to aux_expr.
/// \param sympath: Symbolic path
void heap_domaint::restrict_to_sympath(const symbolic_patht &sympath)
{
  for(auto &row : templ)
  {
    const exprt c=sympath.get_expr(row.pre_guard.op1());
    row.aux_expr=and_exprt(row.aux_expr, c);
  }
}

/// Reset aux symbols to true (remove all restricitions).
void heap_domaint::clear_aux_symbols()
{
  for(auto &row : templ)
    row.aux_expr=true_exprt();
}

/// Restrict template to other paths than those specified.
/// \param sympaths: Vector of symbolic paths
void heap_domaint::eliminate_sympaths(
  const std::vector<symbolic_patht> &sympaths)
{
  for(auto &row : templ)
  {
    exprt::operandst paths;
    for(auto &sympath : sympaths)
    {
      const exprt path_expr=sympath.get_expr(row.pre_guard.op1());
      paths.push_back(path_expr);
    }
    row.aux_expr=paths.empty()
                 ? true_exprt()
                 : static_cast<exprt>(not_exprt(disjunction(paths)));
  }
}

/// Undo last restriction (remove last conjunct from each aux_expr).
void heap_domaint::undo_restriction()
{
  for(auto &row : templ)
  {
    if(row.aux_expr.id()==ID_and)
    {
      row.aux_expr=to_and_expr(row.aux_expr).op0();
    }
  }
}

exprt heap_domaint::get_current_loop_guard(size_t row)
{
  return to_and_expr(templ[row].pre_guard).op1();
}

bool heap_domaint::edit_row(const rowt &row, valuet &_inv, bool improved)
{
  heap_domaint::heap_valuet &inv=
    static_cast<heap_domaint::heap_valuet &>(_inv);
  const heap_domaint::template_rowt &templ_row=templ[row];

  if(templ_row.expr.id()==ID_and)
  {
    // Handle template row with a pair of variables in the expression
    exprt points_to1=get_points_to_dest(
      solver_value_op0,
      templ_row.expr.op0());
    exprt points_to2=get_points_to_dest(
      solver_value_op1,
      templ_row.expr.op1());

    if(points_to1.is_nil() || points_to2.is_nil())
    {
      if(inv[row].set_nondet())
        improved=true;
    }
    else
    {
      if(inv[row].add_points_to(and_exprt(points_to1, points_to2)))
        improved=true;
    }
    return improved;
  }

  exprt points_to=get_points_to_dest(solver_value_op0, templ_row.expr);

  if(points_to.is_nil())
  {
    if(inv[row].set_nondet())
      improved=true;
    return improved;
  }
  else
  {
    if(inv[row].add_points_to(points_to))
      improved=true;
  }

  return improved;
}

/// Get an address where the given pointer points to in the current solver
/// iteration. Returns nil_exprt if the value of the pointer is nondet.
const exprt heap_domaint::get_points_to_dest(
  const exprt &solver_value,
  const exprt &templ_row_expr)
{
  // Value from the solver must be converted into an expression
  exprt ptr_value=value_to_ptr_exprt(solver_value);

  if((ptr_value.id()==ID_constant &&
      to_constant_expr(ptr_value).get_value()==ID_NULL) ||
     ptr_value.id()==ID_symbol)
  {
    // Add equality p == NULL or p == symbol
    return ptr_value;
  }
  else if(ptr_value.id()==ID_address_of)
  {
    // Template row pointer points to the heap (p = &obj)
    assert(ptr_value.id()==ID_address_of);
    if(to_address_of_expr(ptr_value).object().id()!=ID_symbol)
    {
      // If solver did not return address of a symbol, it is considered
      // as nondet value.
      return nil_exprt();
    }

    symbol_exprt obj=to_symbol_expr(
      to_address_of_expr(ptr_value).object());

    if(obj.type()!=templ_row_expr.type() &&
       ns.follow(templ_row_expr.type().subtype())!=ns.follow(obj.type()))
    {
      if(!is_cprover_symbol(templ_row_expr))
      {
        // If types disagree, it's a nondet (solver assigned random value)
        return nil_exprt();
      }
    }

    // Add equality p == &obj
    return obj;
  }
  else
    return nil_exprt();
}
