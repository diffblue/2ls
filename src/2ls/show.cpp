/*******************************************************************\

Module: Showing various debugging information

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Showing various debugging information

#include <util/options.h>
#include <util/find_symbols.h>
#include <util/string2int.h>

#include <goto-programs/read_goto_binary.h>
#include <goto-programs/goto_model.h>
#include <goto-programs/show_properties.h>
#include <goto-programs/set_properties.h>

#include <ssa/ssa_domain.h>
#include <ssa/guard_map.h>
#include <ssa/unwindable_local_ssa.h>
#include <ssa/simplify_ssa.h>
#include <ssa/ssa_value_set.h>

#include <solver/summary.h>

#include "show.h"

void show_assignments(
  const irep_idt &function_identifier,
  const goto_functionst::goto_functiont &goto_function,
  const namespacet &ns,
  const dynamic_objectst &dynamic_objects,
  const optionst &options,
  std::ostream &out)
{
  ssa_objectst ssa_objects(goto_function, ns);
  ssa_value_ait ssa_value_ai(function_identifier, goto_function, ns, options);
  assignmentst assignments(
    goto_function.body,
    ns,
    dynamic_objects,
    options,
    ssa_objects,
    ssa_value_ai);
  assignments.output(ns, goto_function.body, out);
}

void show_assignments(
  const goto_modelt &goto_model,
  const irep_idt &function,
  const dynamic_objectst &dynamic_objects,
  const optionst &options,
  std::ostream &out,
  message_handlert &message_handler)
{
  const namespacet ns(goto_model.symbol_table);

  if(!function.empty())
  {
    goto_functionst::function_mapt::const_iterator
      f_it=goto_model.goto_functions.function_map.find(function);
    if(f_it==goto_model.goto_functions.function_map.end())
      out << "function " << function << " not found\n";
    else
      show_assignments(
        f_it->first, f_it->second, ns, dynamic_objects, options, out);
  }
  else
  {
    for(const auto &f_it : goto_model.goto_functions.function_map)
    {
      out << ">>>> Function " << f_it.first << "\n";

      show_assignments(
        f_it.first, f_it.second, ns, dynamic_objects, options, out);

      out << "\n";
    }
  }
}

void show_defs(
  const irep_idt &function_identifier,
  const goto_functionst::goto_functiont &goto_function,
  const namespacet &ns,
  const dynamic_objectst &dynamic_objects,
  const optionst &options,
  std::ostream &out)
{
  ssa_objectst ssa_objects(goto_function, ns);
  ssa_value_ait ssa_value_ai(function_identifier, goto_function, ns, options);
  assignmentst assignments(
    goto_function.body,
    ns,
    dynamic_objects,
    options,
    ssa_objects,
    ssa_value_ai);
  ssa_ait ssa_analysis(assignments);
  ssa_analysis(function_identifier, goto_function, ns);
  ssa_analysis.output(ns, goto_function, out);
}

void show_defs(
  const goto_modelt &goto_model,
  const irep_idt &function,
  const dynamic_objectst &dynamic_objects,
  const optionst &options,
  std::ostream &out,
  message_handlert &message_handler)
{
  const namespacet ns(goto_model.symbol_table);

  if(!function.empty())
  {
    goto_functionst::function_mapt::const_iterator
      f_it=goto_model.goto_functions.function_map.find(function);
    if(f_it==goto_model.goto_functions.function_map.end())
      out << "function " << function << " not found\n";
    else
      show_defs(f_it->first, f_it->second, ns, dynamic_objects, options, out);
  }
  else
  {
    for(const auto &f_it : goto_model.goto_functions.function_map)
    {
      out << ">>>> Function " << f_it.first << "\n";

      show_defs(f_it.first, f_it.second, ns, dynamic_objects, options, out);

      out << "\n";
    }
  }
}

void show_guards(
  const goto_functionst::goto_functiont &goto_function,
  const namespacet &ns,
  std::ostream &out)
{
  guard_mapt guard_map(goto_function.body);
  guard_map.output(goto_function.body, out);
}

void show_guards(
  const goto_modelt &goto_model,
  const irep_idt &function,
  std::ostream &out,
  message_handlert &message_handler)
{
  const namespacet ns(goto_model.symbol_table);

  if(!function.empty())
  {
    goto_functionst::function_mapt::const_iterator
      f_it=goto_model.goto_functions.function_map.find(function);
    if(f_it==goto_model.goto_functions.function_map.end())
      out << "function " << function << " not found\n";
    else
      show_guards(f_it->second, ns, out);
  }
  else
  {
    for(const auto &f_it : goto_model.goto_functions.function_map)
    {
      out << ">>>> Function " << f_it.first << "\n";

      show_guards(f_it.second, ns, out);

      out << "\n";
    }
  }
}

void show_ssa(
  const irep_idt &function_identifier,
  const goto_functionst::goto_functiont &goto_function,
  bool simplify,
  const symbol_tablet &symbol_table,
  dynamic_objectst &dynamic_objects,
  const optionst &options,
  std::ostream &out)
{
  if(!goto_function.body_available())
    return;

  unwindable_local_SSAt local_SSA(
    function_identifier,
    goto_function,
    symbol_table,
    dynamic_objects,
    options);
  if(simplify)
    ::simplify(local_SSA, local_SSA.ns);
  local_SSA.output_verbose(out);
}

void show_ssa(
  const goto_modelt &goto_model,
  dynamic_objectst &dynamic_objects,
  const optionst &options,
  const irep_idt &function,
  bool simplify,
  std::ostream &out,
  message_handlert &message_handler)
{
  if(!function.empty())
  {
    out << ">>>> Function " << function << "\n";
    goto_functionst::function_mapt::const_iterator
      f_it=goto_model.goto_functions.function_map.find(function);
    if(f_it==goto_model.goto_functions.function_map.end())
      out << "function " << function << " not found\n";
    else
      show_ssa(
        f_it->first,
        f_it->second,
        simplify,
        goto_model.symbol_table,
        dynamic_objects,
        options,
        out);
  }
  else
  {
    for(auto &f_it : goto_model.goto_functions.function_map)
    {
      if(f_it.first=="assert")
        continue;
      if(f_it.first=="__CPROVER_assume")
        continue;

      out << ">>>> Function " << f_it.first << "\n";

      show_ssa(
        f_it.first,
        f_it.second,
        simplify,
        goto_model.symbol_table,
        dynamic_objects,
        options,
        out);

      out << "\n";
    }
  }
}

void print_symbol_values(
  const local_SSAt &SSA,
  prop_convt &solver,
  std::ostream &out,
  const exprt &expr)
{
  if(expr.id()==ID_symbol)
  {
    out << from_expr(SSA.ns, "", expr) << "=="
        << from_expr(SSA.ns, "", solver.get(expr)) << "\n";
    return;
  }
  for(exprt::operandst::const_iterator it=expr.operands().begin();
      it!=expr.operands().end(); it++)
  {
    print_symbol_values(SSA, solver, out, *it);
  }
}

void show_raw_countermodel(
  const irep_idt &property_id,
  const local_SSAt &SSA,
  prop_convt &solver,
  std::ostream &out,
  message_handlert &message_handler)
{
  out << "\n*** Error trace for property " << property_id << "\n";
  for(local_SSAt::nodest::const_iterator n_it=
        SSA.nodes.begin(); n_it!=SSA.nodes.end(); n_it++)
  {
    for(local_SSAt::nodet::equalitiest::const_iterator e_it=
          n_it->equalities.begin(); e_it!=n_it->equalities.end(); e_it++)
    {
      print_symbol_values(SSA, solver, out, *e_it);
      // out << from_expr(SSA.ns, "", e_it->op0()) << "==" <<
      //    from_expr(SSA.ns, "", solver.get(e_it->op0())) << "\n";
    }
    for(local_SSAt::nodet::constraintst::const_iterator c_it=
          n_it->constraints.begin(); c_it!=n_it->constraints.end(); c_it++)
    {
      print_symbol_values(SSA, solver, out, *c_it);
    }
    for(local_SSAt::nodet::assertionst::const_iterator a_it=
          n_it->assertions.begin(); a_it!=n_it->assertions.end(); a_it++)
    {
      print_symbol_values(SSA, solver, out, *a_it);
    }
  }
  out << "\n";
}

local_SSAt::locationt find_loc_by_guard(
  const local_SSAt &SSA,
  const symbol_exprt &guard)
{
  std::string gstr=id2string(guard.get_identifier());
  unsigned pos1=gstr.find("#")+1;
  unsigned pos2=gstr.find("%", pos1);
  unsigned n=safe_string2unsigned(gstr.substr(pos1, pos2));
  return SSA.get_location(n);
}

void purify_identifiers(exprt &expr)
{
  if(expr.id()==ID_symbol)
  {
    std::string idstr=id2string(to_symbol_expr(expr).get_identifier());
    to_symbol_expr(expr).set_identifier(idstr.substr(0, idstr.find("#")));
  }
  for(unsigned i=0; i<expr.operands().size(); i++)
  {
    purify_identifiers(expr.operands()[i]);
  }
}

void show_invariant(
  const local_SSAt &SSA,
  const exprt &expr,
  std::ostream &out)
{
  // expected format (/\_j g_j)=> inv
  const implies_exprt &implies=to_implies_expr(expr);
  const exprt &impl=implies.op0();
  exprt inv=implies.op1(); // copy
  local_SSAt::locationt loc;
  if(impl.id()==ID_symbol)
  {
    loc=find_loc_by_guard(SSA, to_symbol_expr(impl));
  }
  else if(impl.id()==ID_and)
  {
    const and_exprt &conjunction=to_and_expr(impl);
    assert(conjunction.op0().id()==ID_symbol);
    loc=find_loc_by_guard(SSA, to_symbol_expr(conjunction.op0()));
  }
  else
    assert(false);

  out << "\n** invariant: " << loc->source_location << "\n";
  purify_identifiers(inv);
  out << "  " << from_expr(SSA.ns, "", inv) << "\n";
}

void show_invariants(
  const local_SSAt &SSA,
  const summaryt &summary,
  std::ostream &out)
{
  if(summary.fw_invariant.is_nil())
    return;
  if(summary.fw_invariant.is_true())
    return;

  // expected format /\_i g_i=> inv_i
  if(summary.fw_invariant.id()==ID_implies)
  {
    show_invariant(SSA, summary.fw_invariant, out);
  }
  else if(summary.fw_invariant.id()==ID_and)
  {
    for(unsigned i=0; i<summary.fw_invariant.operands().size(); i++)
    {
      assert(summary.fw_invariant.operands()[i].id()==ID_implies);
      show_invariant(SSA, summary.fw_invariant.operands()[i], out);
    }
  }
  else
    assert(false);
}


void show_ssa_symbols(
  const local_SSAt &SSA,
  std::ostream & out)
{
  std::set<symbol_exprt> symbols;
  out << "\n*** SSA Symbols " << "\n";
  for(local_SSAt::nodest::const_iterator n_it=
        SSA.nodes.begin(); n_it!=SSA.nodes.end(); n_it++)
  {
    for(local_SSAt::nodet::equalitiest::const_iterator e_it=
          n_it->equalities.begin(); e_it!=n_it->equalities.end(); e_it++)
    {
      find_symbols(*e_it, symbols);
    }
    for(local_SSAt::nodet::constraintst::const_iterator c_it=
          n_it->constraints.begin(); c_it!=n_it->constraints.end(); c_it++)
    {
      find_symbols(*c_it, symbols);
    }
    for(local_SSAt::nodet::assertionst::const_iterator a_it=
          n_it->assertions.begin(); a_it!=n_it->assertions.end(); a_it++)
    {
      find_symbols(*a_it, symbols);
    }
    find_symbols(n_it->enabling_expr, symbols);
  }

  for(std::set<symbol_exprt>::const_iterator it=symbols.begin();
      it!=symbols.end(); it++)
  {
    out << from_type(SSA.ns, "", it->type()) << " " <<
      from_expr(SSA.ns, "", *it) << ";\n";
  }
  out << "\n";
}

void show_value_set(
  const irep_idt &function_identifier,
  const goto_functionst::goto_functiont &goto_function,
  const namespacet &ns,
  const optionst &options,
  std::ostream &out)
{
  ssa_objectst ssa_objects(goto_function, ns);
  ssa_value_ait ssa_value_ai(function_identifier, goto_function, ns, options);
  ssa_value_ai.output(ns, goto_function, out);
}

void show_value_sets(
  const goto_modelt &goto_model,
  const irep_idt &function,
  const optionst &options,
  std::ostream &out,
  message_handlert &message_handler)
{
  const namespacet ns(goto_model.symbol_table);

  if(!function.empty())
  {
    goto_functionst::function_mapt::const_iterator
      f_it=goto_model.goto_functions.function_map.find(function);
    if(f_it==goto_model.goto_functions.function_map.end())
      out << "function " << function << " not found\n";
    else
      show_value_set(f_it->first, f_it->second, ns, options, out);
  }
  else
  {
    for(const auto &f_it : goto_model.goto_functions.function_map)
    {
      out << ">>>> Function " << f_it.first << "\n";

      show_value_set(f_it.first, f_it.second, ns, options, out);

      out << "\n";
    }
  }
}
