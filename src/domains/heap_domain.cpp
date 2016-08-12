/**
 *  Viktor Malik, 12.8.2016 (c).
 */

#include "heap_domain.h"

void heap_domaint::initialize(domaint::valuet &value)
{
  heap_valuet &val = static_cast<heap_valuet &>(value);
  val.paths.clear();
  val.nulls.clear();
}

void heap_domaint::make_template(const domaint::var_specst &var_specs, const namespacet &ns)
{
  unsigned long size = var_specs.size();
  templ.clear();
  templ.reserve(size);

  for (auto v1 = var_specs.begin(); v1 != var_specs.end(); ++v1)
  {
    // Template for variable - for NULL pointer and dangling checks
    templ.push_back(template_rowt());
    template_rowt &templ_row = templ.back();
    templ_row.expr = v1->var;
    templ_row.pre_guard = v1->pre_guard;
    templ_row.post_guard = v1->post_guard;
    templ_row.aux_expr = v1->post_guard;
    templ_row.kind = v1->kind;
  }
}

exprt heap_domaint::get_pre_null_constraint(unsigned index)
{
  assert(index < templ.size());
  const template_rowt &templ_row = templ[index];
  if (templ_row.kind == OUT || templ_row.kind == OUTL) return true_exprt();
  const vart &var = templ_row.expr;
  return implies_exprt(templ_row.pre_guard,
                       equal_exprt(var, null_pointer_exprt(to_pointer_type(var.type()))));
}

exprt heap_domaint::get_post_not_null_constraint(unsigned index)
{
  assert(index < templ.size());
  const template_rowt &templ_row = templ[index];
  if (templ_row.kind == IN) return true_exprt();
  const vart &var = templ_row.expr;
  exprt c = and_exprt(templ_row.aux_expr,
                      not_exprt(implies_exprt(templ_row.post_guard,
                                              equal_exprt(var, null_pointer_exprt(
                                                  to_pointer_type(var.type()))))));
  rename(c);
  return c;
}

void heap_domaint::set_null(unsigned index, heap_valuet &value)
{
  assert(index < templ.size());
  value.nulls.insert(index);
}

void heap_domaint::get_index_set(std::set<unsigned> &indices)
{
  for (unsigned i = 0; i < templ.size(); i++) indices.insert(i);
}

void heap_domaint::output_value(std::ostream &out, const domaint::valuet &value,
                                const namespacet &ns) const
{
  const heap_valuet &_val = static_cast<const heap_valuet &>(value);
  heap_valuet val = _val;

  for (unsigned i = 0; i < templ.size(); ++i)
  {
    if (val.nulls.find(i) != val.nulls.end())
    {
      out << from_expr(ns, "", templ[i].expr) << "== NULL" << std::endl;
    }
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
    const vart var = templ_row.expr;
    out << from_expr(ns, "", var) << " =!= NULL" << std::endl;
  }
}

void heap_domaint::project_on_vars(domaint::valuet &value,
                                   const domaint::var_sett &vars, exprt &result)
{
  heap_valuet &val = static_cast<heap_valuet &>(value);

  exprt::operandst c;
  for (auto it = val.nulls.begin(); it != val.nulls.end(); ++it)
  {
    const vart &var = templ[*it].expr;

    if (vars.find(var) == vars.end()) continue;

    if (templ[*it].kind == LOOP)
      c.push_back(implies_exprt(templ[*it].pre_guard,
                                equal_exprt(var, null_pointer_exprt(to_pointer_type(var.type())))));
    else
      c.push_back(equal_exprt(var, null_pointer_exprt(to_pointer_type(var.type()))));
  }
  result = conjunction(c);
}
