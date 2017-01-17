/**
 *  Viktor Malik, 12.8.2016 (c).
 */

#include "heap_domain.h"
#include "util.h"
#include "domain.h"
#include <algorithm>
#include <util/symbol.h>

/**
 * Initialize value.
 * Clears each pointer paths and points_to predicates.
 * @param value
 */
void heap_domaint::initialize(domaint::valuet &value)
{
  heap_valuet &val = static_cast<heap_valuet &>(value);

  for (auto &templ_row : templ)
  {
    if (templ_row.mem_kind == STACK)
      val.emplace_back(new stack_row_valuet());
    else if (templ_row.mem_kind == HEAP)
      val.emplace_back(new heap_row_valuet());
    else
      assert(false);
  }
}

/**
 * Create domain template for given set of variables.
 * Template contains a row for each member of each variable being pointer to struct,
 * and a row for each flattened member of a struct.
 * @param var_specs Set of program variables.
 * @param ns Namespace
 */
void heap_domaint::make_template(const domaint::var_specst &var_specs, const namespacet &ns)
{
  unsigned long size = var_specs.size();
  templ.clear();
  templ.reserve(size);

  for (auto v = var_specs.begin(); v != var_specs.end(); ++v)
  {
    if (v->kind == IN) continue;

    // Create template for each pointer to struct
    const vart &var = v->var;
    if (var.type().id() == ID_pointer)
    {
      const typet &pointed_type = ns.follow(var.type().subtype());
      if (pointed_type.id() == ID_struct)
      {
        add_template_row(*v, pointed_type);
      }
    }
  }
}

void heap_domaint::add_template_row(const var_spect &var_spec, const typet &pointed_type)
{
  const vart &var = var_spec.var;

  templ.push_back(template_rowt());
  template_rowt &templ_row = templ.back();
  templ_row.expr = var;
  templ_row.pre_guard = var_spec.pre_guard;
  templ_row.post_guard = var_spec.post_guard;
  templ_row.aux_expr = var_spec.aux_expr;
  templ_row.kind = var_spec.kind;

  templ_row.mem_kind = STACK;
  // Check if var is member field of heap object
  const std::string identifier = id2string(to_symbol_expr(var_spec.var).get_identifier());
  for (auto &component : to_struct_type(pointed_type).components())
  {
    if (identifier.find("." + id2string(component.get_name())) != std::string::npos)
    {
      templ_row.mem_kind = HEAP;
      templ_row.member = component.get_name();

      std::string var_id = id2string(to_symbol_expr(var).get_identifier());
      std::string do_id = var_id.substr(0, var_id.find_last_of('.'));
      templ_row.dyn_obj = symbol_exprt(do_id, var.type().subtype());
    }
  }
}

/**
 * Create entry constraints expression for a value.
 * @param value Value
 * @return Conjuction of entry expressions for each template row
 */
exprt heap_domaint::to_pre_constraints(const heap_domaint::heap_valuet &value) const
{
  assert(value.size() == templ.size());
  exprt::operandst c;
  for (rowt row = 0; row < templ.size(); ++row)
  {
    c.push_back(get_row_pre_constraint(row, value[row]));
  }
  return conjunction(c);
}

/**
 * Create exit constraint expression for each row.
 * Each expression is negation of row expression (for solving exists forall problem).
 * @param value Value
 * @param cond_exprs Output - constraint expressions
 * @param value_exprs Output - template expressions (row variables)
 */
void heap_domaint::make_not_post_constraints(const heap_valuet &value, exprt::operandst &cond_exprs,
                                             exprt::operandst &value_exprs)
{
  assert(value.size() == templ.size());
  cond_exprs.resize(templ.size());
  value_exprs.resize(templ.size());

  for (rowt row = 0; row < templ.size(); ++row)
  {
    value_exprs[row] = templ[row].expr;
    rename(value_exprs[row]);
    cond_exprs[row] = and_exprt(templ[row].aux_expr,
                                not_exprt(get_row_post_constraint(row, value[row])));
  }
}

/**
 * Create entry constraint expression for a row.
 * @param row Row number
 * @param row_value Row value
 * @return Entry constraint expression.
 */
exprt heap_domaint::get_row_pre_constraint(const rowt &row, const row_valuet &row_value) const
{
  assert(row < templ.size());
  const template_rowt &templ_row = templ[row];
  kindt k = templ_row.kind;
  // For exit variables the result is true
  if (k == OUT || k == OUTL) return true_exprt();

  return implies_exprt(templ_row.pre_guard, row_value.get_row_expr(templ_row.expr));
}

/**
 * Create exit constraint expression for a row.
 * @param row Row number
 * @param row_value Row value
 * @return Exit constraint expression.
 */
exprt heap_domaint::get_row_post_constraint(const rowt &row, const row_valuet &row_value)
{
  assert(row < templ.size());
  const template_rowt &templ_row = templ[row];
  // For entry variables the result is true
  if (templ_row.kind == IN) return true_exprt();

  exprt c = implies_exprt(templ_row.post_guard, row_value.get_row_expr(templ_row.expr));
  if (templ_row.kind == LOOP) rename(c);
  return c;
}

/**
 * Add all paths of one pointer as the destinations of another pointer.
 * @param to Row to add new paths to
 * @param from Row to add paths from
 * @param value Heap value
 * @param dyn_obj Dynamic object that all the paths pass through (it belongs to path segment from
 *                one pointer to another.
 * @return True if any path was added or changed, otherwise false.
 */
bool heap_domaint::add_transitivity(const rowt &from, const rowt &to, heap_valuet &value)
{
  assert(from < value.size() && to < value.size());
  assert(templ[to].mem_kind == HEAP && templ[from].mem_kind == HEAP);

  heap_row_valuet &heap_val_from = static_cast<heap_row_valuet &>(value[from]);
  heap_row_valuet &heap_val_to = static_cast<heap_row_valuet &>(value[to]);

  bool result = false;
  if (heap_val_from.add_all_paths(heap_val_to, std::make_pair(templ[to].dyn_obj, templ[to].expr)))
    result = true;
  if (from != to)
  {
    if (heap_val_to.add_pointed_by(from))
      result = true;
  }

  return result;
}

bool heap_domaint::add_points_to(const heap_domaint::rowt &row, heap_domaint::heap_valuet &value,
                                 const exprt &dest)
{
  assert(row < value.size());

  if (templ[row].dyn_obj == dest) return false;

  return value[row].add_points_to(dest);
}

bool heap_domaint::set_nondet(const rowt &row, heap_valuet &value)
{
  assert(row < value.size());

  bool result = !value[row].nondet;
  value[row].nondet = true;
  return result;
}

void heap_domaint::output_value(std::ostream &out, const domaint::valuet &value,
                                const namespacet &ns) const
{
  const heap_valuet &val = static_cast<const heap_valuet &>(value);
  for (rowt row = 0; row < templ.size(); ++row)
  {
    const template_rowt &templ_row = templ[row];
    switch (templ_row.kind)
    {
      case LOOP:
        out << "(LOOP) [ " << from_expr(ns, "", templ_row.pre_guard) << " | ";
        out << from_expr(ns, "", templ_row.post_guard) << " | ";
        out << from_expr(ns, "", templ_row.aux_expr) << " ] ===> " << std::endl << "       ";
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
        << from_expr(ns, "", val[row].get_row_expr(templ_row.expr)) << " )"
        << std::endl;
  }
}

void heap_domaint::output_domain(std::ostream &out, const namespacet &ns) const
{
  for (unsigned i = 0; i < templ.size(); ++i)
  {
    const template_rowt &templ_row = templ[i];
    switch (templ_row.kind)
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
    const vart &var = templ_row.expr;

    out << i << ": " << from_expr(ns, "", var)
        << (templ_row.mem_kind == STACK ? " --points_to--> Locations"
                                        : " --paths--> Destinations")
        << std::endl;
  }
}

void heap_domaint::project_on_vars(domaint::valuet &value,
                                   const domaint::var_sett &vars, exprt &result)
{
  const heap_valuet &val = static_cast<heap_valuet &>(value);
  assert(val.size() == templ.size());

  exprt::operandst c;
  for (rowt row = 0; row < templ.size(); ++row)
  {
    const template_rowt &templ_row = templ[row];

    if (vars.find(templ_row.expr) == vars.end()) continue;

    const row_valuet &row_val = val[row];
    if (templ_row.kind == LOOP)
    {
      c.push_back(implies_exprt(templ_row.pre_guard,
                                row_val.get_row_expr(templ_row.expr)));
    }
    else
    {
      c.push_back(row_val.get_row_expr(templ_row.expr));
    }
  }
  result = conjunction(c);
}

/**
 * Converts constant returned from solver to corresponding expression.
 * @param expr Solver expression
 * @return
 */
exprt heap_domaint::value_to_ptr_exprt(const exprt &expr)
{
  if (expr.id() == ID_constant)
    return expr.op0();

  return expr;
}

/**
 * Join two abstract heap values. Join of each row is union of the two corresponding sets.
 * @param value1 First value and result of join
 * @param value2 Second value
 */
void heap_domaint::join(domaint::valuet &value1, const domaint::valuet &value2)
{
  heap_valuet &val1 = static_cast<heap_valuet &>(value1);
  const heap_valuet &val2 = static_cast<const heap_valuet &>(value2);
  assert(val1.size() == templ.size());
  assert(val2.size() == val1.size());
}

/**
 * Get location number of a given symbol.
 * @param expr Symbol expression.
 * @return Number of location, or -1 if symbol is input.
 */
int heap_domaint::get_symbol_loc(const exprt &expr)
{
  assert(expr.id() == ID_symbol);
  std::string expr_id = id2string(to_symbol_expr(expr).get_identifier());
  if (expr_id.find('#') == std::string::npos) return -1;
  std::string loc_str = expr_id.substr(expr_id.find_last_not_of("0123456789") + 1);
  assert(!loc_str.empty());
  return std::stoi(loc_str);
}

/**
 * Get base name of a symbol.
 * @param expr Symbol expression.
 * @return Base name of a symbol (without suffix with location number).
 */
std::string heap_domaint::get_base_name(const exprt &expr)
{
  assert(expr.id() == ID_symbol);
  std::string result = id2string(to_symbol_expr(expr).get_identifier());
  result = result.substr(0, result.find_last_of('#'));
  return result;
}

exprt heap_domaint::stack_row_valuet::get_row_expr(const domaint::vart &templ_expr) const
{
  if (nondet) return true_exprt();

  if (empty())
    return false_exprt();
  else
  { // Points to expression
    exprt::operandst result;
    for (auto &pt : points_to)
    {
      result.push_back(equal_exprt(templ_expr, templ_expr.type() == pt.type() ?
                                               pt : address_of_exprt(pt)));
    }
    return disjunction(result);
  }
}

bool heap_domaint::stack_row_valuet::add_points_to(const exprt &expr)
{
  auto new_pt = points_to.insert(expr);
  return new_pt.second;
}

exprt heap_domaint::heap_row_valuet::get_row_expr(const domaint::vart &templ_expr) const
{
  if (nondet) return true_exprt();

  if (empty())
    return false_exprt();
  else
  {
    exprt::operandst result;
    for (auto &path : paths)
    { // path(o.m, d)[O]
      const exprt &dest = templ_expr.type() == path.destination.type() ?
                          path.destination : address_of_exprt(path.destination);
      exprt::operandst path_expr;

      // o.m = d
      path_expr.push_back(equal_exprt(templ_expr, dest));

      for (const dyn_objt &obj1 : path.dyn_objects)
      {
        // o.m = &o'
        exprt equ_exprt = equal_exprt(templ_expr, address_of_exprt(obj1.first));

        exprt::operandst steps_expr;
        exprt member_expr = obj1.second;
        // o'.m = d
        steps_expr.push_back(equal_exprt(member_expr, dest));

        for (auto &obj2 : path.dyn_objects)
        { // o'.m = o''
          steps_expr.push_back(equal_exprt(member_expr, address_of_exprt(obj2.first)));
        }

        path_expr.push_back(and_exprt(equ_exprt, disjunction(steps_expr)));
      }

      result.push_back(disjunction(path_expr));
    }
    return conjunction(result);
  }
}

bool heap_domaint::heap_row_valuet::add_points_to(const exprt &dest)
{
  return add_path(dest, std::make_pair(nil_exprt(), nil_exprt()));
}

bool heap_domaint::heap_row_valuet::add_path(const exprt &dest,
                                             const heap_domaint::dyn_objt &dyn_obj)
{
  if (paths.find(dest) == paths.end())
  {
    // Path does not exist yet
    std::set<dyn_objt> dyn_obj_set;
    if (dyn_obj.first.id() != ID_nil)
    { // Path doesn't have zero length
      dyn_obj_set.insert(dyn_obj);
    }
    paths.emplace(dest, dyn_obj_set);
    return true;
  }
  else
  {
    // Path exists already
    if (dyn_obj.first.id() != ID_nil)
      // Try to insert new dynamic object on the path
      return paths.find(dest)->dyn_objects.insert(dyn_obj).second;
    else
      return false;
  }
}

bool heap_domaint::heap_row_valuet::add_all_paths(const heap_domaint::heap_row_valuet &other_val,
                                                  const heap_domaint::dyn_objt &dyn_obj)
{
  bool result = false;
  for (auto &path : other_val.paths)
  {
    // Add the path with new dynamic object
    if (add_path(path.destination, dyn_obj))
      result = true;
    for (auto &o : path.dyn_objects)
    { // Add all dynamic objects of the original path
      if (add_path(path.destination, o))
        result = true;
    }
  }
  return result;
}

bool heap_domaint::heap_row_valuet::add_pointed_by(const rowt &row)
{
  auto new_pb = pointed_by.insert(row);
  return new_pb.second;
}
