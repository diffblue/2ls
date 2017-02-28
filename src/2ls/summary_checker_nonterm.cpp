/*******************************************************************\

Module: Summarizer for Nontermination Bit-level analysis

Author: Stefan Marticek

\*******************************************************************/

#include <iostream>

#include "summary_checker_nonterm.h"

#include <util/i2string.h>
#include <util/simplify_expr.h>
#include <util/prefix.h>

#include <ssa/simplify_ssa.h>
#include <ssa/ssa_var_collector.h>

property_checkert::resultt summary_checker_nontermt::operator()(
  const goto_modelt &goto_model)
{
  /*const namespacet ns(goto_model.symbol_table);

  SSA_functions(goto_model, ns);
  ssa_dbt::functionst& funcs=ssa_db.functions();

  property_checkert::resultt result=property_checkert::UNKNOWN;

  ssa_unwinder.init(false, false);  //is_kinduction, is_bmc - HOW TO SET IT?
  //--k-induction, --incremental-bmc, unwinding?
  ssa_unwinder.init_localunwinders();
  ssa_unwinder.unwind_all(0);

  //unsigned max_unwind = 10;
  for (auto f_ssa_it=funcs.begin(); f_ssa_it!=funcs.end(); ++f_ssa_it)
  {
    local_SSAt &SSA=ssa_db.get(f_ssa_it->first);
    ssa_local_unwindert &ssa_lu=ssa_unwinder.get(f_ssa_it->first);
    ssa_var_collectort ssa_vc=ssa_var_collectort(options, ssa_lu);

    //TODO: replace std::cout with debug()

    std::cout << "\n\n**********>> " << id2string(f_ssa_it->first) << " <<**************\n\n";

    ssa_vc.collect_variables_loop(SSA, true, ns);

    std::cout << "\n\n**********>> " << id2string(f_ssa_it->first) << " <<**************\n\n";

    SSA.output(std::cout);
  }

  return result;*/

  const namespacet ns(goto_model.symbol_table);

  SSA_functions(goto_model, ns);

  ssa_unwinder.init(false, true);

  property_checkert::resultt result=property_checkert::UNKNOWN;
  unsigned max_unwind=options.get_unsigned_int_option("unwind");
  status() << "Max-unwind is " << max_unwind << eom;
  ssa_unwinder.init_localunwinders();

  for(unsigned unwind=0; unwind<=max_unwind; unwind++)
  {
    status() << "Unwinding (k=" << unwind << ")" << messaget::eom;
    summary_db.mark_recompute_all();
    ssa_unwinder.unwind_all(unwind);
    result=summary_checker_baset::check_properties();
    if(result==property_checkert::PASS)
    {
      status() << "incremental BMC proof found after "
         << unwind << " unwinding(s)" << messaget::eom;
      break;
    }
    else if(result==property_checkert::FAIL)
    {
      status() << "incremental BMC counterexample found after "
         << unwind << " unwinding(s)" << messaget::eom;
      break;
    }
  }
  report_statistics();
  return result;
}


/*******************************************************************\

Function: summary_checker_baset::check_properties

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void summary_checker_nontermt::check_properties(
  const ssa_dbt::functionst::const_iterator f_it)
{
  unwindable_local_SSAt &SSA=*f_it->second;

  bool all_properties=options.get_bool_option("all-properties");

  SSA.output_verbose(debug()); debug() << eom;

  // incremental version

  // solver
  incremental_solvert &solver=ssa_db.get_solver(f_it->first);
  solver.set_message_handler(get_message_handler());

  // give SSA to solver
  solver << SSA;
  SSA.mark_nodes();

  solver.new_context();

  exprt enabling_expr=SSA.get_enabling_exprs();
  solver << enabling_expr;

  // freeze loop head selects
  exprt::operandst loophead_selects=
    get_loophead_selects(f_it->first, SSA, *solver.solver);
  // check whether loops have been fully unwound
  exprt::operandst loop_continues=
    get_loop_continues(f_it->first, SSA, *solver.solver);
  bool fully_unwound=
    is_fully_unwound(loop_continues, loophead_selects, solver);
  status() << "Loops " << (fully_unwound ? "" : "not ")
           << "fully unwound" << eom;

  cover_goals_extt cover_goals(
    SSA, solver, loophead_selects, property_map,
    !fully_unwound && options.get_bool_option("spurious-check"),
    all_properties,
    options.get_bool_option("show-trace") ||
    options.get_option("graphml-witness")!="" ||
    options.get_option("json-cex")!="");

#if 0
  debug() << "(C) " << from_expr(SSA.ns, "", enabling_expr) << eom;
#endif

  const goto_programt &goto_program=SSA.goto_function.body;

  for(goto_programt::instructionst::const_iterator
        i_it=goto_program.instructions.begin();
      i_it!=goto_program.instructions.end();
      i_it++)
  {
    if(!i_it->is_assert())
      continue;
  }

  ssa_local_unwindert &ssa_lu=ssa_unwinder.get(f_it->first);
  ssa_var_collectort ssa_vc=ssa_var_collectort(options, ssa_lu);

  std::cout << "\n\n**********>> " << id2string(f_it->first) << " <<**************\n\n";

  ssa_vc.collect_variables_loop(SSA, true, SSA.ns);

//  std::cout << "\n\n**********>> " << id2string(f_it->first) << " <<**************\n\n";


#if 0
        std::cout << "property: " << from_expr(SSA.ns, "", property)
                  << std::endl;
#endif

  for(cover_goals_extt::goal_mapt::const_iterator
        it=cover_goals.goal_map.begin();
      it!=cover_goals.goal_map.end();
      it++)
  {
    // Our goal is to falsify a property.
    // The following is TRUE if the conjunction is empty.
    literalt p=!solver.convert(conjunction(it->second.conjuncts));
    cover_goals.add(p);
  }

  status() << "Running " << solver.solver->decision_procedure_text() << eom;

  cover_goals();

  // set all non-covered goals to PASS except if we do not try
  //  to cover all goals and we have found a FAIL
  if(all_properties || cover_goals.number_covered()==0)
  {
    std::list<cover_goals_extt::cover_goalt>::const_iterator g_it=
      cover_goals.goals.begin();
    for(cover_goals_extt::goal_mapt::const_iterator
          it=cover_goals.goal_map.begin();
        it!=cover_goals.goal_map.end();
        it++, g_it++)
    {
      if(!g_it->covered)
        property_map[it->first].result=PASS;
    }
  }

  solver.pop_context();

  debug() << "** " << cover_goals.number_covered()
          << " of " << cover_goals.size() << " failed ("
          << cover_goals.iterations() << " iterations)" << eom;
}
