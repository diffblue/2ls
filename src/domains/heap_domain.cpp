/*******************************************************************\

Module: Abstract domain for representing heap

Author: Viktor Malik

\*******************************************************************/

#include "heap_domain.h"
#include <algorithm>
#include <ssa/address_canonizer.h>

/*******************************************************************\

Function: heap_domaint::initialize

  Inputs:

 Outputs:

 Purpose: Initialize abstract value.
          Clears value with empty value rows corresponding to template.

\*******************************************************************/

void heap_domaint::initialize(domaint::valuet &value)
{
  heap_valuet &val=static_cast<heap_valuet &>(value);

  for(const template_rowt &templ_row : templ)
  {
    if(templ_row.mem_kind==STACK)
      val.emplace_back(new stack_row_valuet());
    else if(templ_row.mem_kind==HEAP)
      val.emplace_back(
        new heap_row_valuet(std::make_pair(templ_row.dyn_obj, templ_row.expr)));
    else
      assert(false);
  }
}

/*******************************************************************\

Function: heap_domaint::make_template

  Inputs:

 Outputs:

 Purpose: Create domain template for given set of variables.
          Template contains a row for each pointer-typed variable and 
          field of a dynamic object.

\*******************************************************************/

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
    }
  }
}

/*******************************************************************\

Function: heap_domaint::add_template_row

  Inputs: var_spec Variable specification

 Outputs:

 Purpose: Add a template row.

\*******************************************************************/

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

  templ_row.mem_kind=STACK;
  if(pointed_type.id()==ID_struct)
  {
    // Check if var is member field of heap object
    const std::string identifier=id2string(
      to_symbol_expr(var_spec.var).get_identifier());
    for(auto &component : to_struct_type(pointed_type).components())
    {
      if(identifier.find("."+id2string(component.get_name()))!=
         std::string::npos)
      {
        templ_row.mem_kind=HEAP;
        templ_row.member=component.get_name();

        std::string var_id=id2string(to_symbol_expr(var).get_identifier());
        std::string do_id=var_id.substr(0, var_id.find_last_of('.'));
        templ_row.dyn_obj=symbol_exprt(do_id, var.type().subtype());
      }
    }
  }
}

/*******************************************************************\

Function: heap_domaint::to_pre_constraints

  Inputs:

 Outputs: Entry constraints expression for a value.

 Purpose: Create entry constraints as a conjuction of entry
 expressions for each template row.

\*******************************************************************/

exprt heap_domaint::to_pre_constraints(const heap_valuet &value) const
{
  assert(value.size()==templ.size());
  exprt::operandst c;
  for(rowt row=0; row<templ.size(); ++row)
  {
    c.push_back(get_row_pre_constraint(row, value[row]));
  }
  return conjunction(c);
}

/*******************************************************************\

Function: heap_domaint::make_not_post_constraints

  Inputs:

 Outputs: Exit constraint expression for each row.

 Purpose: Create exit constraints for each value row.
          Each expression is a negation of a row expression
          (for solving the "exists forall" problem).

\*******************************************************************/

void heap_domaint::make_not_post_constraints(
  const heap_valuet &value,
  exprt::operandst &cond_exprs,
  exprt::operandst &value_exprs)
{
  assert(value.size()==templ.size());
  cond_exprs.resize(templ.size());
  value_exprs.resize(templ.size());

  for(rowt row=0; row<templ.size(); ++row)
  {
    value_exprs[row]=templ[row].expr;
    rename(value_exprs[row]);
    cond_exprs[row]=and_exprt(templ[row].aux_expr, not_exprt(
      get_row_post_constraint(row, value[row])));
  }
}

/*******************************************************************\

Function: heap_domaint::get_row_pre_constraint

  Inputs:

 Outputs: Exit constraint expression for each row.

 Purpose: Create entry constraint expression for a row.

\*******************************************************************/

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

  if(k==OUTHEAP && row_value.empty())
    return true_exprt();

  return implies_exprt(
    templ_row.pre_guard, row_value.get_row_expr(templ_row.expr, false));
}

/*******************************************************************\

Function: heap_domaint::get_row_post_constraint

  Inputs:

 Outputs: Exit constraint expression for each row.

 Purpose: Create exit constraint expression for a row.

\*******************************************************************/

exprt heap_domaint::get_row_post_constraint(
  const rowt &row,
  const row_valuet &row_value)
{
  assert(row<templ.size());
  const template_rowt &templ_row=templ[row];
  // For entry variables the result is true
  if(templ_row.kind==IN)
    return true_exprt();

  exprt c=implies_exprt(
    templ_row.post_guard, row_value.get_row_expr(
      templ_row.expr, templ_row.kind==OUTHEAP));
  if(templ_row.kind==LOOP)
    rename(c);
  return c;
}

/*******************************************************************\

Function: heap_domaint::add_transitivity

  Inputs: to Row to add new paths to
          from Row to add paths from
          dyn_obj Dynamic object that all the paths pass through (it belongs to
                  path segment from one pointer to another).

 Outputs: True if any path was added or changed, otherwise false.

 Purpose: Add all paths of one pointer as the destinations of another pointer.

\*******************************************************************/

bool heap_domaint::add_transitivity(
  const rowt &from,
  const rowt &to,
  heap_valuet &value)
{
  assert(from<value.size() && to<value.size());
  assert(templ[to].mem_kind==HEAP && templ[from].mem_kind==HEAP);

  heap_row_valuet &heap_val_from=static_cast<heap_row_valuet &>(value[from]);
  heap_row_valuet &heap_val_to=static_cast<heap_row_valuet &>(value[to]);

  bool result=false;
  if(heap_val_from.add_all_paths(
    heap_val_to, std::make_pair(
      templ[to].dyn_obj, templ[to].expr)))
    result=true;
  if(from!=to)
  {
    if(heap_val_to.add_pointed_by(from))
      result=true;
  }

  return result;
}

/*******************************************************************\

Function: heap_domaint::add_points_to

  Inputs:

 Outputs:

 Purpose: Add new object pointed by a row.
          Calls add_points_to of the given row.
          For stack rows, the destination is simply added into pointed 
          objects set.
          For heap rows, a new path is added.

\*******************************************************************/

bool heap_domaint::add_points_to(
  const rowt &row,
  heap_valuet &value,
  const exprt &dest)
{
  assert(row<value.size());
  return value[row].add_points_to(dest);
}

/*******************************************************************\

Function: heap_domaint::set_nondet

  Inputs:

 Outputs:

 Purpose: Set row nondeterministic.

\*******************************************************************/

bool heap_domaint::set_nondet(const rowt &row, heap_valuet &value)
{
  assert(row<value.size());

  bool result=!value[row].nondet;
  value[row].nondet=true;
  return result;
}

/*******************************************************************\

Function: heap_domaint::output_value

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

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
    case OUTHEAP:
      out << "(HEAP)  ";
      break;
    default:
      assert(false);
    }
    out << "( " << from_expr(ns, "", templ_row.expr) << " == "
        << from_expr(ns, "", val[row].get_row_expr(templ_row.expr, false))
        << " )"
        << std::endl;
  }
}

/*******************************************************************\

Function: heap_domaint::output_domain

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

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
    case OUTHEAP:
      out << "(HEAP) [ " << from_expr(ns, "", templ_row.pre_guard) << " | ";
      out << from_expr(ns, "", templ_row.post_guard)
          << " ] ===> " << std::endl << "      ";
      break;
    default:
      assert(false);
    }
    const vart &var=templ_row.expr;

    out << i << ": " << from_expr(ns, "", var)
      << (templ_row.mem_kind==STACK ? " --points_to--> Locations"
                                    : " --paths--> Destinations")
        << std::endl;
  }
}

/*******************************************************************\

Function: heap_domaint::project_on_vars

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

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

    if(vars.find(templ_row.expr)==vars.end())
      continue;

    const row_valuet &row_val=val[row];
    if(templ_row.kind==LOOP)
    {
      c.push_back(
        implies_exprt(
          templ_row.pre_guard, row_val.get_row_expr(templ_row.expr, false)));
    }
    else
    {
      exprt row_expr=row_val.get_row_expr(templ_row.expr, false);
      if(templ_row.kind==OUTHEAP)
        rename(row_expr);
      c.push_back(row_expr);
    }
  }
  result=conjunction(c);
}

/*******************************************************************\

Function: heap_domaint::value_to_ptr_exprt

  Inputs:

 Outputs:

 Purpose: Converts a constant returned from the solver to
          the corresponding expression.

\*******************************************************************/

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

/*******************************************************************\

Function: heap_domaint::join

  Inputs:

 Outputs:

 Purpose: Not used.

\*******************************************************************/

void heap_domaint::join(domaint::valuet &value1, const domaint::valuet &value2)
{
  heap_valuet &val1=static_cast<heap_valuet &>(value1);
  const heap_valuet &val2=static_cast<const heap_valuet &>(value2);
  assert(val1.size()==templ.size());
  assert(val2.size()==val1.size());
}

/*******************************************************************\

Function: heap_domaint::get_symbol_loc

  Inputs: Symbol expression.

 Outputs: Number of location, or -1 if symbol is input.

 Purpose: Get location number of a given symbol.

\*******************************************************************/

int heap_domaint::get_symbol_loc(const exprt &expr)
{
  assert(expr.id()==ID_symbol);
  std::string expr_id=id2string(to_symbol_expr(expr).get_identifier());
  if(expr_id.find('#')==std::string::npos) return -1;
  std::string loc_str=expr_id.substr(expr_id.find_last_not_of("0123456789")+1);
  assert(!loc_str.empty());
  return std::stoi(loc_str);
}

/*******************************************************************\

Function: heap_domaint::get_base_name

  Inputs: Symbol expression.

 Outputs: Base name of a symbol (without suffix with location number).

 Purpose: Get base name of a symbol.

\*******************************************************************/

std::string heap_domaint::get_base_name(const exprt &expr)
{
  assert(expr.id()==ID_symbol);
  std::string result=id2string(to_symbol_expr(expr).get_identifier());
  result=result.substr(0, result.find_last_of('#'));
  return result;
}

/*******************************************************************\

Function: heap_domaint::stack_row_valuet::get_row_expr

  Inputs: templ_expr Template expression

 Outputs: Formula corresponding to the template row

 Purpose: Stack row is a disjuction of equalities between templ_expr
          and addresses of dynamic objects from points_to set.

\*******************************************************************/

exprt heap_domaint::stack_row_valuet::get_row_expr(const vart &templ_expr,
                                                   bool rename_templ_expr) const
{
  if(nondet)
    return true_exprt();

  if(empty())
    return false_exprt();
  else
  { 
    // Points to expression
    exprt::operandst result;
    for(const exprt &pt : points_to)
    {
      result.push_back(equal_exprt(templ_expr, templ_expr.type()==pt.type() ?
                                               pt : address_of_exprt(pt)));
    }
    return disjunction(result);
  }
}

/*******************************************************************\

Function: heap_domaint::stack_row_valuet::add_points_to

  Inputs:

 Outputs:

 Purpose: Add new object to the value of a stack row. The object is
          simply added to the set.

\*******************************************************************/

bool heap_domaint::stack_row_valuet::add_points_to(const exprt &expr)
{
  auto new_pt=points_to.insert(expr);
  return new_pt.second;
}

/*******************************************************************\

Function: heap_domaint::heap_row_valuet::get_row_expr

  Inputs: templ_expr Template expression
          rename_templ_expr True if templ_expr should be renamed
                            (the corresponding template row is of
                            OUTHEAP type)

 Outputs: Formula corresponding to the template row

 Purpose: Heap row is disjunction of path sets, where each path set is a conjunction of paths.

          nondet is TRUE
          empty is FALSE

\*******************************************************************/

exprt heap_domaint::heap_row_valuet::get_row_expr(const vart &templ_expr_,
                                                  bool rename_templ_expr) const
{
  if(nondet) return true_exprt();

  exprt templ_expr=templ_expr_;
  if(rename_templ_expr)
    templ_expr=rename_outheap(to_symbol_expr(templ_expr_));

  if(paths.empty())
  {
    if(self_linkage)
    {
      return equal_exprt(templ_expr, address_of_exprt(dyn_obj.first));
    }
    else
      return false_exprt();
  }
  else
  {
    exprt::operandst result;
    for(const pathsett &path_set : paths)
    {
      exprt::operandst path_set_expr;
      for(const patht &path : path_set)
      { // path(o.m, d)[O]
        const exprt &dest=templ_expr.type()==path.destination.type() ?
                          path.destination : address_of_exprt(path.destination);
        exprt::operandst path_expr;

        // o.m = d
        path_expr.push_back(equal_exprt(templ_expr, dest));

        for(const dyn_objt &obj1 : path.dyn_objects)
        {
          // o.m = &o'
          exprt equ_exprt=equal_exprt(templ_expr, address_of_exprt(obj1.first));

          exprt::operandst steps_expr;
          exprt member_expr=obj1.second;
          // o'.m = d
          steps_expr.push_back(equal_exprt(member_expr, dest));

          for(const dyn_objt &obj2 : path.dyn_objects)
          { 
            // o'.m = o''
            steps_expr.push_back(equal_exprt(member_expr, address_of_exprt(obj2.first)));
          }

          path_expr.push_back(and_exprt(equ_exprt, disjunction(steps_expr)));
        }

        path_set_expr.push_back(disjunction(path_expr));
      }
      result.push_back(conjunction(path_set_expr));
    }
    return disjunction(result);
  }
}

/*******************************************************************\

Function: heap_domaint::heap_row_valuet::add_points_to

  Inputs:

 Outputs:

 Purpose: Add new object to heap row - create new path, or set
          self_linkage flag in case the object is same as the row
          object.

\*******************************************************************/

bool heap_domaint::heap_row_valuet::add_points_to(const exprt &dest)
{
  if(dest==dyn_obj.first)
  {
    return add_self_linkage();
  }
  else
  {
    const dyn_objt through=self_linkage ? dyn_obj : std::make_pair(nil_exprt(),
                                                                   nil_exprt());
    return add_path(dest, through);
  }
}

/*******************************************************************\

Function: heap_domaint::heap_row_valuet::add_path

  Inputs: dest Path destination
          dyn_obj Dynamic object that the path goes through

 Outputs: True if the value was changed (a path was added)

 Purpose: Add new path set if any path set does not contain
          the given destination.

          If any path set already contains dest, do nothing since
          the pathset will be updated from other rows.

\*******************************************************************/

bool heap_domaint::heap_row_valuet::add_path(
  const exprt &dest,
  const dyn_objt &dyn_obj)
{
  bool new_path=true;
  for(const pathsett &path_set : paths)
  {
    auto p_it=path_set.find(dest);
    if(p_it!=path_set.end() && p_it->dyn_objects.empty())
    {
      new_path=false;
      break;
    }
  }
  if(new_path)
  {
    pathsett new_path_set;
    std::set<dyn_objt> dyn_obj_set;
    if(dyn_obj.first.id()!=ID_nil)
    {
      dyn_obj_set.insert(dyn_obj);
    }
    if(self_linkage)
    {
      dyn_obj_set.insert(this->dyn_obj);
    }
    new_path_set.emplace(dest, dyn_obj_set);
    paths.push_back(new_path_set);
  }
  return new_path;
}

/*******************************************************************\

Function: heap_domaint::heap_row_valuet::add_path

  Inputs: dest Path destination
          dyn_obj Dynamic object that the path goes through
          path_set Path set to add the path to

 Outputs: True if the value was changed (a path was added)

 Purpose: Add new path to a path set

\*******************************************************************/

bool heap_domaint::heap_row_valuet::add_path(
  const exprt &dest,
  const dyn_objt &dyn_obj,
  pathsett &path_set)
{
  if(path_set.find(dest)==path_set.end())
  {
    // Path does not exist yet
    std::set<dyn_objt> dyn_obj_set;
    if(dyn_obj.first.id()!=ID_nil)
    { // Path doesn't have zero length
      dyn_obj_set.insert(dyn_obj);
    }
    if(self_linkage)
    {
      dyn_obj_set.insert(this->dyn_obj);
    }
    path_set.emplace(dest, dyn_obj_set);
    return true;
  }
  else
  {
    // Path exists already
    if(dyn_obj.first.id()!=ID_nil)
      // Try to insert new dynamic object on the path
      return path_set.find(dest)->dyn_objects.insert(dyn_obj).second;
    else
      return false;
  }
}

/*******************************************************************\

Function: heap_domaint::heap_row_valuet::join_path_sets

  Inputs: src Source path set
          dest Destination path set

 Outputs: True if the value was changed (dest was added)

 Purpose: Join two path sets. Add all paths from src to dest.

\*******************************************************************/

bool heap_domaint::heap_row_valuet::join_path_sets(
  pathsett &dest,
  const pathsett &src,
  const dyn_objt &through)
{
  bool result=false;
  for(const patht &path : src)
  {
    if(add_path(path.destination, through, dest))
      result=true;
    for(const dyn_objt &o : path.dyn_objects)
    { // Add all dynamic objects of the original path
      if(add_path(path.destination, o, dest))
        result=true;
    }
  }
  return result;
}

/*******************************************************************\

Function: heap_domaint::heap_row_valuet::add_all_paths

  Inputs:

 Outputs: True if this has changed

 Purpose: Add all paths from other heap row.

\*******************************************************************/

bool heap_domaint::heap_row_valuet::add_all_paths(
  const heap_row_valuet &other_val,
  const dyn_objt &dyn_obj)
{
  bool result=false;

  auto other_it=other_val.paths.begin();
  if(other_it!=other_val.paths.end())
  {
    for(auto it=paths.begin(); it!=paths.end(); ++it)
    {
      if(it->find(other_val.dyn_obj.first)!=it->end())
      {
        auto next_it=other_it;
        ++next_it;
        if(next_it!=other_val.paths.end())
        { // Duplicate element pointed by it
          auto n_it=it;
          ++n_it;
          paths.insert(n_it, *it);
        }

        // Add all paths to *it

        if(join_path_sets(*it, *other_it, dyn_obj))
          result=true;

        // Move other_it to next, or to first if next doesn't exist
        other_it=
          next_it==other_val.paths.end() ? other_val.paths.begin() : next_it;
      }
    }
  }
  return result;
}

/*******************************************************************\

Function: heap_domaint::heap_row_valuet::add_pointed_by

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool heap_domaint::heap_row_valuet::add_pointed_by(const rowt &row)
{
  auto new_pb=pointed_by.insert(row);
  return new_pb.second;
}

/*******************************************************************\

Function: heap_domaint::heap_row_valuet::add_self_linkage

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool heap_domaint::heap_row_valuet::add_self_linkage()
{
  bool result;
  result=!self_linkage;
  self_linkage=true;
  if(result)
  {
    for(const pathsett &path_set : paths)
    {
      for(const patht &path : path_set)
      {
        path.dyn_objects.insert(dyn_obj);
      }
    }
  }
  return result;
}

/*******************************************************************\

Function: heap_domaint::heap_row_valuet::rename_outheap

  Inputs: expr Expression to be renamed

 Outputs: Renamed expression

 Purpose: Rename OUTHEAP row expression (used for post-expr).
          Simply remove 'lb' from suffix.

\*******************************************************************/

exprt heap_domaint::heap_row_valuet::rename_outheap(const symbol_exprt &expr)
{
  const std::string id=id2string(expr.get_identifier());
  return symbol_exprt(id.substr(0, id.rfind("lb"))+id.substr(id.rfind("lb")+2),
                      expr.type());
}

/*******************************************************************\

Function: heap_domaint::get_new_heap_vars

  Inputs:

 Outputs: List of variables (symbols) that were added to template
          during analysis.

 Purpose:

\*******************************************************************/

const std::list<symbol_exprt> heap_domaint::get_new_heap_vars()
{
  std::list<symbol_exprt> result;
  for(const template_rowt &row : templ)
  {
    if(row.kind==OUTHEAP)
    {
      assert(row.expr.id()==ID_symbol);
      symbol_exprt expr=to_symbol_expr(row.expr);
      rename(expr);
      result.push_back(expr);
    }
  }
  return result;
}

/*******************************************************************\

Function: heap_domaint::initialize_domain

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void heap_domaint::initialize_domain(
  const local_SSAt &SSA,
  const exprt &precondition,
  template_generator_baset &template_generator)
{
  // Bind list iterators
  bind_iterators(SSA, precondition, template_generator);

  // Create preconditions for input variables if not exist
  exprt::operandst equs;
  for(const symbol_exprt &param : SSA.params)
    create_precondition(param, precondition);
  for(const symbol_exprt &global_in : SSA.globals_in)
    create_precondition(global_in, precondition);
}

/*******************************************************************\

Function: heap_domaint::bind_iterators

  Inputs: SSA
          precondition Calling context
          template_generator

 Outputs:

 Purpose: Bind iterators from SSA to actual heap objects from the
          calling context.

\*******************************************************************/

void heap_domaint::bind_iterators(
  const local_SSAt &SSA,
  const exprt &precondition,
  template_generator_baset &template_generator)
{
  new_heap_row_specs.clear();
  for(const list_iteratort &iterator : SSA.iterators)
  {
    for(const list_iteratort::accesst &access : iterator.accesses)
    {
      exprt access_binding=iterator_access_bindings(
        iterator.pointer,
        iterator.init_pointer,
        iterator.iterator_symbol(),
        iterator.fields,
        access,
        0,
        exprt::operandst(),
        precondition,
        SSA);

      // Special treatment for first element in the list
      // @TODO this should be handled better
      if(access.fields.size()>1 && access.location!=list_iteratort::IN_LOC)
      {
        const std::set<exprt> first=collect_preconditions_rec(
          iterator.init_pointer,
          precondition);
        for(const exprt &value : first)
        {
          if(value.id()==ID_address_of)
          {
            assert(to_address_of_expr(value).object().id()==ID_symbol);
            const symbol_exprt &first_obj=to_symbol_expr(
              to_address_of_expr(value).object());
            const symbol_exprt new_value=recursive_member_symbol(
              first_obj, access.fields.back(), access.location, ns);
            const symbol_exprt old_value=recursive_member_symbol(
              first_obj, access.fields.back(), list_iteratort::IN_LOC, ns);
            const exprt binding=equal_exprt(new_value, old_value);
            access_binding=or_exprt(access_binding, binding);

            add_new_heap_row_spec(old_value, (unsigned) access.location,
                                  binding);
          }
        }
      }

      iterator_bindings.push_back(access_binding);
    }
  }

  // Add template rows for bound heap objects
  for(const heap_row_spect &row_spec : new_heap_row_specs)
  {
    new_output_template_row(
      row_spec.expr, row_spec.location_number, row_spec.post_guard, SSA,
      template_generator);
  }
}

/*******************************************************************\

Function: heap_domaint::new_output_template_row

  Inputs:

 Outputs:

 Purpose: Insert new output template row into the template.

\*******************************************************************/

void heap_domaint::new_output_template_row(
  const symbol_exprt &var,
  const unsigned location_number,
  const exprt &post_guard,
  const local_SSAt &SSA,
  template_generator_baset &template_generator)
{
  template_generator.var_specs.push_back(domaint::var_spect());
  domaint::var_spect &var_spec=template_generator.var_specs.back();

  local_SSAt::locationt loc=SSA.get_location(location_number);

  const exprt pre_guard=SSA.guard_symbol(loc);

  const symbol_exprt pre_var=SSA.name(
    ssa_objectt(var, SSA.ns), local_SSAt::LOOP_BACK, loc);
  const symbol_exprt post_var=SSA.name(
    ssa_objectt(var, SSA.ns), local_SSAt::OUT, loc);

  var_spec.var=pre_var;
  var_spec.pre_guard=pre_guard;
  var_spec.post_guard=post_guard;
  var_spec.aux_expr=true_exprt();
  var_spec.kind=OUTHEAP;

  renaming_map[pre_var]=post_var;

  assert(var.type().id()==ID_pointer);
  const typet &pointed_type=ns.follow(var.type().subtype());
  add_template_row(var_spec, pointed_type);
}

/*******************************************************************\

Function: heap_domaint::create_precondition

  Inputs: Variable and a calling context (precondition)

 Outputs:

 Purpose: Create precondition for given variable at the input of the
          function if it does not exist in given calling context.

\*******************************************************************/

void heap_domaint::create_precondition(
  const symbol_exprt &var,
  const exprt &precondition)
{
  if(var.type().id()==ID_pointer)
  {
    auto pre=collect_preconditions_rec(var, precondition);
    if(pre.empty() || (pre.size()==1 && *(pre.begin())==var))
    {
      if(id2string(var.get_identifier()).find('.')==std::string::npos)
      {
        // For variables, create abstract address
        const symbolt *symbol;
        if(ns.lookup(id2string(var.get_identifier()), symbol))
          return;

        address_of_exprt init_value(symbol->symbol_expr());
        init_value.type()=symbol->type;
        aux_bindings.push_back(equal_exprt(var, init_value));
      }
      else
      {
        // For members of structs, find corresponding object in the calling
        // context and return its member
        std::string var_id_str=id2string(var.get_identifier());
        const symbol_exprt pointer(
          var_id_str.substr(0, var_id_str.rfind("'obj")), var.type());
        const irep_idt member=var_id_str.substr(var_id_str.rfind("."));

        exprt::operandst d;
        std::set<exprt> pointed_objs=collect_preconditions_rec(
          pointer, precondition);
        for(exprt pointed : pointed_objs)
        {
          if(pointed.id()==ID_address_of)
          {
            const exprt pointed_object=to_address_of_expr(pointed).object();
            if(pointed_object.id()==ID_symbol)
            {
              symbol_exprt pointed_member(
                id2string(to_symbol_expr(pointed_object).get_identifier())+
                id2string(member),
                var.type());
              d.push_back(equal_exprt(var, pointed_member));
            }
          }
        }
        if(!d.empty())
        {
          iterator_bindings.push_back(disjunction(d));
        }
      }
    }
  }
}

/*******************************************************************\

Function: heap_domaint::get_iterator_bindings

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

const exprt heap_domaint::get_iterator_bindings() const
{
  return conjunction(iterator_bindings);
}

/*******************************************************************\

Function: heap_domaint::get_aux_bindings

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

const exprt heap_domaint::get_aux_bindings() const
{
  return conjunction(aux_bindings);
}

/*******************************************************************\

Function: heap_domaint::get_input_bindings

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

const exprt heap_domaint::get_input_bindings() const
{
  return and_exprt(get_iterator_bindings(), get_aux_bindings());
}

/*******************************************************************\

Function: heap_domaint::iterator_access_bindings

  Inputs: src Source pointer (symbolic value)
          init_pointed Actual value of the source pointer
          iterator_sym Corresponding iterator symbol
          fields Set of fields to follow
          access Iterator access to be bound
          level Current access level
          guards
          precondition Calling context
          SSA

 Outputs: Formula corresponding to bindings

 Purpose: Create bindings of iterator with corresponding dynamic objects.
          Function is called recursively, if there is access with multiple
          fields.

\*******************************************************************/

const exprt heap_domaint::iterator_access_bindings(
  const symbol_exprt &src,
  const exprt &init_pointer,
  const symbol_exprt &iterator_sym,
  const std::vector<irep_idt> &fields,
  const list_iteratort::accesst &access,
  const unsigned level,
  exprt::operandst guards,
  const exprt &precondition,
  const local_SSAt &SSA)
{
  const std::set<symbol_exprt> reachable=reachable_objects(
    init_pointer, fields, precondition);

  exprt::operandst d;
  for(const symbol_exprt &r : reachable)
  {
    exprt::operandst c;

    equal_exprt points_to_eq(src, address_of_exprt(r));
    c.push_back(points_to_eq);

    if(level==0)
    {
      equal_exprt address_eq(
        address_canonizer(address_of_exprt(iterator_sym), ns),
        address_of_exprt(r));
      c.push_back(address_eq);
    }

    equal_exprt access_eq=access.binding(iterator_sym, r, level, ns);
    c.push_back(access_eq);

    guards.push_back(conjunction(c));

    if(level<access.fields.size()-1)
    {
      assert(access_eq.lhs().id()==ID_symbol);
      assert(access_eq.rhs().id()==ID_symbol);
      const symbol_exprt new_src=to_symbol_expr(access_eq.rhs());
      const symbol_exprt new_iterator_sym=pointed_object(
        to_symbol_expr(access_eq.lhs()), ns);
      c.push_back(
        iterator_access_bindings(
          new_src, r, new_iterator_sym, {access.fields.at(level)}, access,
          level+1, guards, precondition, SSA));
    }
    else if(access.location!=list_iteratort::IN_LOC)
    {
      add_new_heap_row_spec(
        recursive_member_symbol(r, access.fields.back(), list_iteratort::IN_LOC,
                                ns),
        (unsigned) access.location, conjunction(guards));
    }

    guards.pop_back();

    d.push_back(conjunction(c));
  }

  if(!d.empty())
    return disjunction(d);
  else
    return true_exprt();
}

/*******************************************************************\

Function: heap_domaint::reachable_objects

  Inputs: src Source expression
          fields Set of fields to follow
          precondition Calling context

 Outputs: Set of reachable objects

 Purpose: Find all objects reachable from source via the vector of fields

\*******************************************************************/

const std::set<symbol_exprt> heap_domaint::reachable_objects(
  const exprt &src,
  const std::vector<irep_idt> &fields,
  const exprt &precondition) const
{
  std::set<symbol_exprt> result;

  if(!(src.id()==ID_symbol || src.id()==ID_member)) return result;

  std::set<symbol_exprt> pointed_objs;
  if(src.id()==ID_member && to_member_expr(src).compound().get_bool(ID_pointed))
  {
    const member_exprt &member=to_member_expr(src);
    const exprt pointer=get_pointer(member.compound(),
                                    pointed_level(member.compound())-1);

    std::set<symbol_exprt> r=reachable_objects(
      pointer, {member.get_component_name()}, precondition);
    pointed_objs.insert(r.begin(), r.end());
  }
  else
  {
    if(src.type().id()==ID_pointer)
    {
      std::set<exprt> values=collect_preconditions_rec(src, precondition);
      for(const exprt &v : values)
      {
        if(v.id()==ID_address_of)
        {
          assert(to_address_of_expr(v).object().id()==ID_symbol);
          pointed_objs.insert(to_symbol_expr(to_address_of_expr(v).object()));
        }
      }
    }
    else
    {
      assert(src.type().get_bool("#dynamic"));
      pointed_objs.insert(to_symbol_expr(src));
    }
  }

  for(unsigned i=0; i<fields.size(); ++i)
  {
    for(const symbol_exprt &pointed_obj : pointed_objs)
    {
      // Create obj.member
      symbol_exprt obj_member=recursive_member_symbol(pointed_obj, fields.at(i),
                                                      list_iteratort::IN_LOC,
                                                      ns);

      // Collect all reachable objects (from heap rows of the calling context)
      std::set<exprt> reachable_objs=collect_preconditions_rec(
        obj_member, precondition);
      for(const exprt &reachable : reachable_objs)
      {
        if(reachable.id()==ID_address_of)
        {
          const exprt &reachable_obj=to_address_of_expr(reachable).object();
          assert(reachable_obj.id()==ID_symbol);

          result.insert(to_symbol_expr(reachable_obj));
        }
      }
    }
    if(i!=fields.size()-1)
      pointed_objs=result;
  }

  return result;
}

/*******************************************************************\

Function: heap_domaint::add_new_heap_row_spec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void heap_domaint::add_new_heap_row_spec(
  const symbol_exprt &expr,
  const unsigned location_number,
  const exprt &post_guard)
{
  auto it=new_heap_row_specs.emplace(expr, location_number, post_guard);
  if(!it.second)
  {
    if(it.first->post_guard!=post_guard)
      it.first->post_guard=or_exprt(it.first->post_guard, post_guard);
  }
}

/*******************************************************************\

Function: heap_domaint::collect_preconditions_rec

  Inputs: Expression and calling context (precondition)

 Outputs: Set of preconditions corresponding to given expression.

 Purpose: Recursively find all preconditions for the given expression
          in the calling context.
          Returns right-hand sides of equalities where expr is left-hand
          side.

\*******************************************************************/

const std::set<exprt> heap_domaint::collect_preconditions_rec(
  const exprt &expr,
  const exprt &precondition)
{
  std::set<exprt> result;
  if(precondition.id()==ID_equal)
  {
    const equal_exprt &eq=to_equal_expr(precondition);
    if((eq.lhs()==expr && eq.rhs()!=expr) ||
       (eq.lhs().id()==ID_symbol &&
        expr.id()==ID_symbol &&
        to_symbol_expr(eq.lhs()).get_identifier()==
        to_symbol_expr(expr).get_identifier()))
    {
      result.insert(eq.rhs());
    }
  }
  else
  {
    forall_operands(it, precondition)
    {
      std::set<exprt> op_result=collect_preconditions_rec(expr, *it);
      result.insert(op_result.begin(), op_result.end());
    }
  }
  return result;
}
