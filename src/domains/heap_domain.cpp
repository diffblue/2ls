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

  for(const template_rowt &templ_row : templ)
  {
    if(templ_row.mem_kind==STACK)
      val.emplace_back(new stack_row_valuet(ns));
    else if(templ_row.mem_kind==HEAP)
      val.emplace_back(
        new heap_row_valuet(
          ns,
          std::make_pair(
            templ_row.dyn_obj,
            templ_row.expr)));
    else
      assert(false);
  }
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
#if 0
        // It has shown that using stack rows only is sufficient to prove all
        // tested programs and it seems that pointer access paths are not
        // necessary. Therefore, we currently disable this code.
        templ_row.mem_kind=HEAP;
#endif
        templ_row.member=component.get_name();

        std::string var_id=id2string(to_symbol_expr(var).get_identifier());
        std::string do_id=var_id.substr(0, var_id.find_last_of('.'));
        templ_row.dyn_obj=symbol_exprt(do_id, var.type().subtype());
      }
    }
  }
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

  templ_row.mem_kind=STACK;
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

  if(k==OUTHEAP && row_value.empty())
    return true_exprt();

  const exprt row_expr=row_value.get_row_expr(templ_row.expr, false);
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
    row_value.get_row_expr(templ_row.expr, templ_row.kind==OUTHEAP);
  exprt c=implies_exprt(templ_row.post_guard, row_expr);
  if(templ_row.kind==LOOP)
    rename(c);
  return c;
}

/// Add all paths of one pointer as the destinations of another pointer.
/// \param from: Row to add paths from
/// \param to: Row to add new paths to
/// \param value: Dynamic object that all the paths pass through
///   (it belongs to path segment from one pointer to another).
/// \return True if any path was added or changed, otherwise false.
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
    heap_val_to,
    std::make_pair(templ[to].dyn_obj, templ[to].expr)))
  {
    result=true;
  }
  if(from!=to)
  {
    if(heap_val_to.add_pointed_by(from))
      result=true;
  }

  return result;
}

/// Add new object pointed by a row. Calls add_points_to of the given row. For
/// stack rows, the destination is simply added into pointed  objects set. For
/// heap rows, a new path is added.
bool heap_domaint::add_points_to(
  const rowt &row,
  heap_valuet &value,
  const exprt &dest)
{
  assert(row<value.size());
  return value[row].add_points_to(dest);
}

/// Set row nondeterministic.
bool heap_domaint::set_nondet(const rowt &row, heap_valuet &value)
{
  assert(row<value.size());

  bool result=!value[row].nondet;
  value[row].nondet=true;
  return result;
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

    const std::string info=
      templ_row.mem_kind==STACK
      ? " --points_to--> Locations"
      : " --paths--> Destinations";
    out << i << ": " << from_expr(ns, "", var) << info << std::endl;
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
      const exprt row_expr=row_val.get_row_expr(templ_row.expr, false);
      c.push_back(implies_exprt(templ_row.pre_guard, row_expr));
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

/// Stack row is a disjuction of equalities between templ_expr and addresses of
/// dynamic objects from points_to set.
/// \param templ_expr: Template expression
/// \param rename_templ_expr: Unused
/// \return Formula corresponding to the template row
exprt heap_domaint::stack_row_valuet::get_row_expr(
  const vart &templ_expr,
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
}

/// Add new object to the value of a row. The object is simply added to the set.
bool heap_domaint::stack_row_valuet::add_points_to(const exprt &expr)
{
  if(points_to.find(expr)==points_to.end())
    points_to.insert(expr);
  else
    nondet=true;
  return true;
}

/// Clear stack row value
void heap_domaint::stack_row_valuet::clear()
{
  nondet=false;
  points_to.clear();
}

/// Heap row is a conjunction of paths:
///   nondet is TRUE
///   empty is FALSE
/// \param templ_expr: Template expression
/// \param rename_templ_expr: True if templ_expr should be renamed
///   (the corresponding template row is of OUTHEAP type)
/// \return Formula corresponding to the template row
exprt heap_domaint::heap_row_valuet::get_row_expr(
  const vart &templ_expr_,
  bool rename_templ_expr) const
{
  if(nondet)
    return true_exprt();

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
    for(const patht &path : paths)
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
          steps_expr.push_back(
            equal_exprt(
              member_expr,
              address_of_exprt(obj2.first)));
        }

        path_expr.push_back(and_exprt(equ_exprt, disjunction(steps_expr)));
      }

      result.push_back(disjunction(path_expr));
    }
    return conjunction(result);
  }
}

/// Add new object to the heap row - create new path or set self_linkage flag in
/// case the object is same as the row object.
bool heap_domaint::heap_row_valuet::add_points_to(const exprt &dest)
{
  if(dest==dyn_obj.first)
  {
    if(!add_self_linkage())
      nondet=true;
  }
  else
  {
    const dyn_objt through=
      self_linkage ? dyn_obj : std::make_pair(nil_exprt(), nil_exprt());
    if(!add_path(dest, through))
      nondet=true;
  }
  return true;
}

/// Add new path to the heap row
/// \param dest: Path destination
/// \param dyn_obj: Dynamic object that the path goes through
/// \return True if the value was changed (a path was added)
bool heap_domaint::heap_row_valuet::add_path(
  const exprt &dest,
  const dyn_objt &dyn_obj)
{
  if(paths.find(dest)==paths.end())
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
    paths.emplace(dest, dyn_obj_set);
    return true;
  }
  else
  {
    // Path exists already
    if(dyn_obj.first.id()!=ID_nil)
      // Try to insert new dynamic object on the path
      return paths.find(dest)->dyn_objects.insert(dyn_obj).second;
    else
      return false;
  }
}

/// Add all paths from other heap row.
/// \return True if this has changed
bool heap_domaint::heap_row_valuet::add_all_paths(
  const heap_row_valuet &other_val,
  const dyn_objt &dyn_obj)
{
  bool result=false;
  for(auto &path : other_val.paths)
  {
    bool new_dest=(paths.find(path.destination)==paths.end());
    if(add_path(path.destination, dyn_obj))
    {
      if(!new_dest)
        paths.erase(dyn_obj.first);
      result=true;
      for(auto &o : path.dyn_objects)
      {
        if(add_path(path.destination, o))
          result=true;
      }
    }
  }
  return result;
}

bool heap_domaint::heap_row_valuet::add_pointed_by(const rowt &row)
{
  auto new_pb=pointed_by.insert(row);
  return new_pb.second;
}

bool heap_domaint::heap_row_valuet::add_self_linkage()
{
  bool result;
  result=!self_linkage;
  self_linkage=true;
  if(result)
  {
    for(const patht &path : paths)
    {
      path.dyn_objects.insert(dyn_obj);
    }
  }
  return result;
}

/// Rename OUTHEAP row expression (used for post-expr). Simply remove 'lb' from
/// suffix.
/// \param expr: Expression to be renamed
/// \return Renamed expression
exprt heap_domaint::heap_row_valuet::rename_outheap(const symbol_exprt &expr)
{
  const std::string id=id2string(expr.get_identifier());
  return symbol_exprt(
    id.substr(0, id.rfind("lb"))+id.substr(id.rfind("lb")+2),
    expr.type());
}

/// \return Clear heap row value
void heap_domaint::heap_row_valuet::clear()
{
  nondet=false;
  paths.clear();
}

/// \return List of variables (symbols) that were added to template during
///   analysis.
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

/// Bind iterators in the \p template_generator from \p SSA to actual heap
/// objects from the calling context given by \p precondition
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
            const symbol_exprt &first_obj=
              to_symbol_expr(to_address_of_expr(value).object());
            const symbol_exprt new_value=
              recursive_member_symbol(
                first_obj,
                access.fields.back(),
                access.location,
                ns);
            const symbol_exprt old_value=
              recursive_member_symbol(
                first_obj,
                access.fields.back(),
                list_iteratort::IN_LOC,
                ns);
            const exprt binding=equal_exprt(new_value, old_value);
            access_binding=or_exprt(access_binding, binding);

            add_new_heap_row_spec(
              old_value,
              static_cast<unsigned>(access.location),
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
      row_spec.expr,
      row_spec.location_number,
      row_spec.post_guard,
      SSA,
      template_generator);
  }
}

/// Insert new output template row into the template.
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

  const symbol_exprt pre_var=
    SSA.name(ssa_objectt(var, SSA.ns), local_SSAt::LOOP_BACK, loc);
  const symbol_exprt post_var=
    SSA.name(ssa_objectt(var, SSA.ns), local_SSAt::OUT, loc);

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

/// Create \p precondition for given \p var at the input of the function if it
/// does not exist in given calling context.
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
          var_id_str.substr(0, var_id_str.rfind("'obj")),
          var.type());
        const irep_idt member=var_id_str.substr(var_id_str.rfind("."));

        exprt::operandst d;
        std::set<exprt> pointed_objs=
          collect_preconditions_rec(pointer, precondition);
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

exprt heap_domaint::get_iterator_bindings() const
{
  return conjunction(iterator_bindings);
}

exprt heap_domaint::get_aux_bindings() const
{
  return conjunction(aux_bindings);
}

exprt heap_domaint::get_input_bindings() const
{
  return and_exprt(get_iterator_bindings(), get_aux_bindings());
}

/// Create bindings of iterator with corresponding dynamic objects. Function is
/// called recursively, if there is access with multiple fields.
/// \param src: Source pointer (symbolic value)
/// \param init_pointed: Actual value of the source pointer
/// \param iterator_sym: Corresponding iterator symbol
/// \param fields: Set of fields to follow
/// \param access: Iterator access to be bound
/// \param level: Current access level
/// \param guards: Guards
/// \param precondition: Calling context
/// \param SSA: SSA
/// \return Formula corresponding to bindings
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
  const std::set<symbol_exprt> reachable=
    reachable_objects(init_pointer, fields, precondition);

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
          new_src,
          r,
          new_iterator_sym,
          {access.fields.at(level)},
          access,
          level+1,
          guards,
          precondition,
          SSA));
    }
    else if(access.location!=list_iteratort::IN_LOC)
    {
      add_new_heap_row_spec(
        recursive_member_symbol(
          r,
          access.fields.back(),
          list_iteratort::IN_LOC,
          ns),
        static_cast<unsigned>(access.location),
        conjunction(guards));
    }

    guards.pop_back();

    d.push_back(conjunction(c));
  }

  if(!d.empty())
    return disjunction(d);
  else
    return true_exprt();
}

/// Find all objects reachable from source via the vector of fields
/// \param src: Source expression
/// \param fields: Set of fields to follow
/// \param precondition: Calling context
/// \return Set of reachable objects
const std::set<symbol_exprt> heap_domaint::reachable_objects(
  const exprt &src,
  const std::vector<irep_idt> &fields,
  const exprt &precondition) const
{
  std::set<symbol_exprt> result;

  if(!(src.id()==ID_symbol || src.id()==ID_member))
    return result;

  std::set<symbol_exprt> pointed_objs;
  if(src.id()==ID_member && to_member_expr(src).compound().get_bool(ID_pointed))
  {
    const member_exprt &member=to_member_expr(src);
    const exprt pointer=
      get_pointer(member.compound(), pointed_level(member.compound())-1);

    std::set<symbol_exprt> r=
      reachable_objects(pointer, {member.get_component_name()}, precondition);
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

  for(std::size_t i=0; i<fields.size(); ++i)
  {
    for(const symbol_exprt &pointed_obj : pointed_objs)
    {
      // Create obj.member
      symbol_exprt obj_member=recursive_member_symbol(
        pointed_obj,
        fields.at(i),
        list_iteratort::IN_LOC,
        ns);

      // Collect all reachable objects (from heap rows of the calling context)
      std::set<exprt> reachable_objs=collect_preconditions_rec(
        obj_member,
        precondition);
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

/// Recursively find all preconditions for the given expression in the calling
/// context. Returns right-hand sides of equalities where expr is left-hand
/// side.
/// \param expr: Expression
/// \param precondition: calling context
/// \return Set of preconditions corresponding to given expression.
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
      if(set_nondet(row, inv))
      {
        improved=true;
      }
    }
    else
    {
      if(add_points_to(
        row, inv, and_exprt(points_to1, points_to2)))
      {
        improved=true;
        const std::string info=
          templ_row.mem_kind==heap_domaint::STACK ? "points to "
                                                  : "path to ";
      }
    }
    return improved;
  }

  int actual_loc=get_symbol_loc(templ_row.expr);

  exprt points_to=get_points_to_dest(solver_value_op0, templ_row.expr);

  if(points_to.is_nil())
  {
    if(set_nondet(row, inv))
    {
      improved=true;
    }
    return improved;
  }
  else
  {
    if(add_points_to(row, inv, points_to))
    {
      improved=true;
      const std::string info=
        templ_row.mem_kind==heap_domaint::STACK ? "points to "
                                                : "path to ";
    }
  }

  // If the template row is of heap kind, we need to ensure the
  // transitive closure over the set of all paths
  if(templ_row.mem_kind==heap_domaint::HEAP &&
     points_to.type().get_bool("#dynamic") &&
     points_to.id()==ID_symbol &&
     id2string(to_symbol_expr(points_to).get_identifier()).find(
       "$unknown")==
     std::string::npos)
  {
    // Find row with corresponding member field of the pointed object
    // (obj.member)
    int member_val_index;
    member_val_index=
      find_member_row(
        points_to,
        templ_row.member,
        actual_loc,
        templ_row.kind);
    if(member_val_index>=0 && !inv[member_val_index].nondet)
    {
      // Add all paths from obj.next to p
      if(add_transitivity(
        row,
        static_cast<unsigned>(member_val_index),
        inv))
      {
        improved=true;
        const std::string expr_str=
          from_expr(ns, "", templ[member_val_index].expr);
      }
    }
  }

  // Recursively update all rows that are dependent on this row
  if(templ_row.mem_kind==heap_domaint::HEAP)
  {
    updated_rows.clear();
    if(!inv[row].nondet)
      update_rows_rec(row, inv);
    else
      clear_pointing_rows(row, inv);
  }

  return improved;
}


/// Find the template row that contains specified member field of a dynamic
/// object at the given location.
/// \param obj: Object
/// \param member: Object field
/// \param actual_loc: Actual location
/// \param kind: Kind
/// \return Row number for obj.member#loc with maximal loc less than actual_loc
///   -1 if such template row does not exist
int heap_domaint::find_member_row(
  const exprt &obj,
  const irep_idt &member,
  int actual_loc,
  const domaint::kindt &kind)
{
  assert(obj.id()==ID_symbol);
  std::string obj_id=id2string(
    ssa_inlinert::get_original_identifier(to_symbol_expr(obj)));

  int result=-1;
  int max_loc=-1;
  for(unsigned i=0; i<templ.size(); ++i)
  {
    heap_domaint::template_rowt &templ_row=templ[i];
    if(templ_row.kind==kind && templ_row.member==member &&
       templ_row.mem_kind==heap_domaint::HEAP)
    {
      std::string id=id2string(to_symbol_expr(templ_row.expr).get_identifier());
      if(id.find(obj_id)!=std::string::npos &&
         id.find_first_of(".")==obj_id.length())
      {
        int loc=get_symbol_loc(templ_row.expr);
        if(loc>max_loc &&
           (kind==domaint::OUT || kind==domaint::OUTHEAP || loc<=actual_loc))
        {
          max_loc=loc;
          result=i;
        }
      }
    }
  }
  return result;
}

/// Recursively update rows that point to given row.
bool heap_domaint::update_rows_rec(
  const heap_domaint::rowt &row,
  heap_domaint::heap_valuet &value)
{
  heap_domaint::heap_row_valuet &row_value=
    static_cast<heap_domaint::heap_row_valuet &>(value[row]);
  const heap_domaint::template_rowt &templ_row=templ[row];

  updated_rows.insert(row);
  bool result=false;
  for(const heap_domaint::rowt &ptr : row_value.pointed_by)
  {
    if(templ[ptr].mem_kind==heap_domaint::HEAP &&
      templ[ptr].member==templ_row.member)
    {
      if(add_transitivity(ptr, row, value))
        result=true;

      // Recursive update is called for each row only once
      if(updated_rows.find(ptr)==updated_rows.end())
        result=update_rows_rec(ptr, value) || result;
    }
  }
  return result;
}

const exprt heap_domaint::initialize_solver(
  const local_SSAt &SSA,
  const exprt &precondition,
  template_generator_baset &template_generator)
{
  initialize_domain(SSA, precondition, template_generator);

  const exprt input_bindings=get_input_bindings();
  if(!input_bindings.is_true())
  {
    return input_bindings;
  }
  return true_exprt();
}


void heap_domaint::clear_pointing_rows(
  const heap_domaint::rowt &row,
  heap_domaint::heap_valuet &value)
{
  heap_domaint::heap_row_valuet &row_value=
    static_cast<heap_domaint::heap_row_valuet &>(value[row]);

  std::vector<heap_domaint::rowt> to_remove;
  for(auto &ptr : row_value.pointed_by)
  {
    if(ptr!=row)
    {
      value[ptr].clear();
      to_remove.push_back(ptr);
    }
  }
  for(auto &r : to_remove)
    row_value.pointed_by.erase(r);
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
