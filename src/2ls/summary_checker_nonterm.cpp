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
#include <2ls/show.h>

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
  ssa_unwinder.unwind_all(10);

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

    //std::cout << SSA;
    SSA.output(std::cout);
  }

  return result;*/

  const namespacet ns(goto_model.symbol_table);

  SSA_functions(goto_model, ns);

  // loop_map needs to be initialized somewhere
  // works only with inline argument which is automatically set with nontermination
  unwindable_local_SSAt &SSA=*(ssa_db.functions().begin()->second);
  for(local_SSAt::nodest::const_iterator n_it = SSA.nodes.begin();
    n_it != SSA.nodes.end(); n_it++)
  {
    if(n_it->loophead != SSA.nodes.end())
    {
      loop_map[n_it->loophead->location->location_number]=
          var_collectort();
    }
  }

  ssa_unwinder.init(false, true);

  property_checkert::resultt result=property_checkert::UNKNOWN;
  unsigned max_unwind=options.get_unsigned_int_option("unwind");
  status() << "Max-unwind is " << max_unwind << eom;
  ssa_unwinder.init_localunwinders();

  for(unsigned unwind=0; unwind<=max_unwind; unwind++)
  {
    status() << "Unwinding (k=" << unwind << ")" << messaget::eom;
    ssa_unwinder.unwind_all(unwind);
    result=summary_checker_baset::check_properties();
    //this is turned - look at it later after getting better result form cover goals
    if(result==property_checkert::PASS)
    {
      status() << "Unable to proof nontermination after "
         << unwind << " unwinding(s)" << messaget::eom;
      break;
    }
    else if(result==property_checkert::FAIL)
    {
      status() << "Nonterminating program execution proved after "
         << unwind << " unwinding(s)" << messaget::eom;
      break;
    }
  }
  report_statistics();
  return result;
}

void summary_checker_nontermt::check_properties(
  const ssa_dbt::functionst::const_iterator f_it)
{
  unwindable_local_SSAt &SSA=*f_it->second;

  ssa_local_unwindert &ssa_local_unwinder=ssa_unwinder.get(f_it->first);

  bool all_properties=options.get_bool_option("all-properties");

  SSA.output_verbose(debug()); debug() << eom;
  SSA.output_verbose(std::cout);

  // incremental version

  // solver
  incremental_solvert &solver=ssa_db.get_solver(f_it->first);
  solver.set_message_handler(get_message_handler());

  // give SSA to solver
  solver << SSA;
  SSA.mark_nodes();

  solver.new_context();

  // freeze loop head selects
  exprt::operandst loophead_selects=
    get_loophead_selects(f_it->first, SSA, *solver.solver);

  exprt enabling_expr=SSA.get_enabling_exprs();
  solver << enabling_expr;

  cover_goals_extt cover_goals(
    SSA, solver, loophead_selects, property_map,
    false,
    all_properties,
    options.get_bool_option("show-trace") ||
    options.get_option("graphml-witness")!="" ||
    options.get_option("json-cex")!="");

#if 0
  debug() << "(C) " << from_expr(SSA.ns, "", enabling_expr) << eom;
#endif

  property_map.clear();

  exprt::operandst ls_guards;

  ssa_local_unwinder.compute_loop_continuation_conditions();

  for(local_SSAt::nodest::const_iterator n_it = SSA.nodes.begin();
        n_it != SSA.nodes.end(); n_it++)
  {
    if(n_it->loophead != SSA.nodes.end()) //we've found a loop
    {
      //const source_locationt &location=n_it->loophead->location->source_location;
      irep_idt property_id=irep_idt(n_it->loophead->location->location_number,
                                    0);

      exprt lhguard = SSA.guard_symbol(n_it->loophead->location);
      ssa_local_unwinder.unwinder_rename(to_symbol_expr(lhguard),*n_it,true);
      exprt lsguard = SSA.name(SSA.guard_symbol(),
             local_SSAt::LOOP_SELECT, n_it->location);
      ssa_local_unwinder.unwinder_rename(to_symbol_expr(lsguard),*n_it,true);

      const ssa_domaint::phi_nodest &phi_nodes=
        SSA.ssa_analysis[n_it->loophead->location].phi_nodes;

      loop_varst loop_vars(lhguard);

      for(local_SSAt::objectst::const_iterator
          o_it=SSA.ssa_objects.objects.begin();
          o_it!=SSA.ssa_objects.objects.end();
          o_it++)
      {
        ssa_domaint::phi_nodest::const_iterator p_it=
        phi_nodes.find(o_it->get_identifier());
        if(p_it==phi_nodes.end()) continue; // object not modified in this loop

        symbol_exprt post_var=SSA.read_rhs(*o_it, n_it->location);
        ssa_local_unwinder.unwinder_rename(post_var,*n_it,false);

        symbol_exprt phi_var;
        phi_var=SSA.name(*o_it, local_SSAt::PHI, n_it->loophead->location);
        ssa_local_unwinder.unwinder_rename(phi_var,*n_it->loophead,true);

        loop_vars.loop_vars_eq.push_back(equal_exprt(post_var, phi_var));
      }

      unsigned loop_idx=
          n_it->loophead->location->location_number;
      loop_map[loop_idx].push_back(loop_vars);

      exprt::operandst loop_check_operands;

      for (var_collectort::iterator it=loop_map[loop_idx].begin();
           it != loop_map[loop_idx].end();
           ++it)
      {
        loop_check_operands.push_back(and_exprt(and_exprt(it->loop_guard,
                                             conjunction(it->loop_vars_eq),
              ssa_local_unwinder.get_loop_countinuation_conditions(loop_idx))));
        std::cout << "Loop id: " << loop_idx << std::endl;
        std::cout << "gueard: " << from_expr(SSA.ns, "", it->loop_guard) << std::endl;
        std::cout << "vars: " << from_expr(SSA.ns, "", ssa_local_unwinder.get_loop_countinuation_conditions(loop_idx)) << std::endl;
      }

      property_map[property_id].location=n_it->loophead->location;
      property_map[property_id].result=UNKNOWN;
      cover_goals.goal_map[property_id].conjuncts.push_back(
            disjunction(loop_check_operands));
      ls_guards.push_back(not_exprt(lsguard));
    }
  }

  /*exprt::operandst in_loop_conds;
  ssa_local_unwinder.loop_continuation_conditions(in_loop_conds);
  solver << conjunction(in_loop_conds);*/
  solver << conjunction(ls_guards);

  for(cover_goals_extt::goal_mapt::const_iterator
        it=cover_goals.goal_map.begin();
      it!=cover_goals.goal_map.end();
      it++)
  {
    // Our goal is to falsify a property.
    // The following is TRUE if the conjunction is empty.
    /*solver << conjunction(it->second.conjuncts);
    switch(solver())
    {
    case decision_proceduret::D_UNSATISFIABLE: //
        std::cout << "Unsat++++++++++++++++" << std::endl;
      break;

    case decision_proceduret::D_SATISFIABLE:
      std::cout << "Sat++++++++++++++++" << std::endl;
      break;

    default:
      error() << "decision procedure has failed" << eom;
      return;
    }*/

    literalt p=solver.convert(conjunction(it->second.conjuncts));
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
      //if(!g_it->covered)
        //property_map[it->first].result=PASS;
    }
  }

  solver.pop_context();

  std::cout << "** " << cover_goals.number_covered()
          << " of " << cover_goals.size() << " failed ("
          << cover_goals.iterations() << " iterations)" << eom;
}
