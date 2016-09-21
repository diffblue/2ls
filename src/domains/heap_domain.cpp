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
  val.resize(templ.size());
  for (unsigned row = 0; row < templ.size(); ++row)
  {
    val[row].paths.clear();
    val[row].points_to.clear();
  }
}

/**
 * Create domain template for given set of variables.
 * Template contains row for each member of each variable being pointer to struct,
 * and a row for each flattened member of a struct.
 * @param var_specs Set of program variables.
 * @param ns Namespace
 */
void heap_domaint::make_template(const domaint::var_specst &var_specs, const namespacet &ns)
{
  unsigned long size = var_specs.size();
  templ.clear();
  templ.reserve(size);

  for (auto v1 = var_specs.begin(); v1 != var_specs.end(); ++v1)
  {
    // Create template for each pointer to struct
    const vart &var1 = v1->var;
    if (var1.type().id() == ID_pointer)
    {
      const typet &pointed_type = ns.follow(var1.type().subtype());
      if (pointed_type.id() == ID_struct)
      {
        // Check if var1 is member field of dynamic object
        const std::string identifier = id2string(to_symbol_expr(v1->var).get_identifier());
        bool dynamic = identifier.find("dynamic_object$") != std::string::npos;

        for (auto &component : to_struct_type(pointed_type).components())
        {
          if (!dynamic ||
              identifier.find("." + id2string(component.get_name())) != std::string::npos)
          {
            templ.push_back(template_rowt());
            template_rowt &templ_row = templ.back();
            templ_row.expr = v1->var;
            templ_row.member = component.get_name();
            templ_row.pre_guard = v1->pre_guard;
            templ_row.post_guard = v1->post_guard;
            templ_row.aux_expr = v1->aux_expr;
            templ_row.kind = v1->kind;
            templ_row.dynamic = dynamic;
            if (dynamic)
            {
              int loc_num = get_symbol_loc(var1);
              std::string var1_id = id2string(to_symbol_expr(var1).get_identifier());
              std::string do_base_id = var1_id.substr(0, var1_id.find_last_of('.'));
              // TODO just add the whole suffix
              irep_idt do_id = do_base_id + "#lb" + std::to_string(loc_num);
              templ_row.dyn_obj = symbol_exprt(do_id, var1.type().subtype());
            }
            else
              templ_row.dyn_obj = nil_exprt();
          }
        }
      }
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
 * Add new destination for a row
 * @param row Row number
 * @param value Value
 * @param dest New destination to add
 * @param dyn_obj Dynamic object for that the path passes through (is nil if path can have zero
 *        length).
 * @return True if insertion took place (dest did not exist in the row value)
 */
bool heap_domaint::add_row_path(const rowt &row, heap_valuet &value, const exprt &dest,
                                const dyn_objt &dyn_obj)
{
  assert(row < value.size());
  assert(value.size() == templ.size());

  auto &path_set = value[row].paths;

  if (path_set.find(dest) == path_set.end())
  {
    // Path does not exist yet
    std::set<dyn_objt> dyn_obj_set;
    bool zero_path = true;
    if (dyn_obj.first.id() != ID_nil)
    { // Path doesn't have zero length
      dyn_obj_set.insert(dyn_obj);
      zero_path = false;
    }
    path_set.emplace(dest, dyn_obj_set, zero_path);
    return true;
  }
  else
  {
    // Path exists already
    if (dyn_obj.first.id() == ID_nil)
    {
      bool result = path_set.find(dest)->zero_length;
      path_set.find(dest)->zero_length = true;
      return !result;
    }
    // Try to insert new dynamic object belonging to the path
    return path_set.find(dest)->dyn_objects.insert(dyn_obj).second;
  }
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
bool heap_domaint::add_all_paths(const rowt &to, const rowt &from, heap_valuet &value,
                                 const dyn_objt &dyn_obj)
{
  bool result = false;
  for (auto &path : value[from].paths)
  {
    // Add the path with new dynamic object
    if (add_row_path(to, value, path.destination, dyn_obj))
      result = true;
    for (auto &o : path.dyn_objects)
    { // Add all dynamic objects of the original path
      if (add_row_path(to, value, path.destination, o))
        result = true;
    }
  }
  return result;
}

/**
 * Add new points to address to a row.
 * @param row Value row
 * @param value Heap value
 * @param dyn_obj New dynamic object that the row variable can point to.
 * @return True if the object was really added.
 */
bool heap_domaint::add_points_to(const rowt &row, heap_valuet &value, const dyn_objt &dyn_obj)
{
  auto new_pt = value[row].points_to.insert(dyn_obj);
  return new_pt.second;
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
    const irep_idt &member = templ_row.member;
    out << i << ": ?path(" << from_expr(ns, "", var) << ", " << member << ", DESTINATIONS)"
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
  for (rowt row = 0; row < templ.size(); ++row)
  { // Insert all elements of second set to first
    val1[row].paths.insert(val2[row].paths.begin(), val2[row].paths.end());
  }
}

/**
 * Check whether expression is NULL pointer.
 * @param expr Expression to check
 * @return True if expr is NULL pointer
 */
bool heap_domaint::is_null_ptr(const exprt &expr)
{
  if (expr.id() == ID_constant && to_constant_expr(expr).get_value() == ID_NULL)
    return true;
  if (expr.id() == ID_plus)
    return is_null_ptr(expr.op0()) || is_null_ptr(expr.op1());
  if (expr.id() == ID_typecast)
    return is_null_ptr(to_typecast_expr(expr).op());
  return false;
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
