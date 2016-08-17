/**
 *  Viktor Malik, 12.8.2016 (c).
 */

#include "heap_domain.h"
#include "util.h"

/**
 * Initialize value.
 * Clears each pointer destinations.
 * @param value
 */
void heap_domaint::initialize(domaint::valuet &value)
{
  heap_valuet &val = static_cast<heap_valuet &>(value);
  val.resize(templ.size());
  for (unsigned row = 0; row < templ.size(); ++row)
    val[row].dests.clear();
}

/**
 * Create domain template for given set of variables.
 * Template contains only pointers to structures containing field 'next'.
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
    // Check if v1 is struct and has 'next' field
    bool has_next = false;
    const vart &var1 = v1->var;
    if (var1.type().id() == ID_pointer)
    {
      const typet &pointed_type = ns.follow(var1.type().subtype());
      if (pointed_type.id() == ID_struct)
      {
        for (auto &component : to_struct_type(pointed_type).components())
        {
          if (component.get_name() == "next")
            has_next = true;
        }
      }
    }

    if (has_next)
    { // Create template
      templ.push_back(template_rowt());
      template_rowt &templ_row = templ.back();
      templ_row.expr = v1->var;
      templ_row.pre_guard = v1->pre_guard;
      templ_row.post_guard = v1->post_guard;
      templ_row.aux_expr = v1->post_guard;
      templ_row.kind = v1->kind;
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
 * @param cond_exprs Constraint expressions
 * @param value_exprs Template expressions (variables)
 */
void heap_domaint::make_not_post_constraints(const heap_domaint::heap_valuet &value,
                                             exprt::operandst &cond_exprs,
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
  if (row_value.dests.empty())
    // Bottom is false
    return implies_exprt(templ_row.pre_guard, false_exprt());
  return implies_exprt(templ_row.pre_guard, row_value.get_row_expr(templ_row.expr, ns));
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
  if (row_value.dests.empty())
    // Bottom is false
    return implies_exprt(templ_row.post_guard, false_exprt());
  exprt c = implies_exprt(templ_row.post_guard, row_value.get_row_expr(templ_row.expr, ns));
  if (templ_row.kind == LOOP) rename(c);
  return c;
}

/**
 * Add new destination for a row
 * @param row Row number
 * @param value Value
 * @param dest New destination to add
 * @return True if insertion took place (dest did not exist in the row value)
 */
bool heap_domaint::add_row_dest(const heap_domaint::rowt &row,
                                heap_domaint::heap_valuet &value,
                                const exprt &dest)
{
  assert(row < value.size());
  assert(value.size() == templ.size());
  auto new_dest = value[row].dests.insert(dest);
  return new_dest.second;
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
        << from_expr(ns, "", val[row].get_row_expr(templ_row.expr, ns)) << " )" << std::endl;
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
    out << "?path(" << from_expr(ns, "", var) << ", DESTINATIONS)" << std::endl;
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
      if (row_val.dests.empty())
        c.push_back(implies_exprt(templ_row.pre_guard, false_exprt()));
      else
        c.push_back(implies_exprt(templ_row.pre_guard, row_val.get_row_expr(templ_row.expr, ns)));
    }
    else
    {
      if (row_val.dests.empty())
        c.push_back(false_exprt());
      else
        c.push_back(row_val.get_row_expr(templ_row.expr, ns));
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
