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
  const namespacet ns(goto_model.symbol_table);

  SSA_functions(goto_model, ns);

  ssa_unwinder.init(false, true);

  property_checkert::resultt result=property_checkert::UNKNOWN;
  unsigned max_unwind=options.get_unsigned_int_option("unwind");
  status() << "Max-unwind is " << max_unwind << eom;
  ssa_unwinder.init_localunwinders();

  /*unsigned unwind;

  unwind=2;

  if (result==property_checkert::UNKNOWN)
  {
    ssa_unwinder.unwind_all(unwind);
    result=check_nonterm_linear();
    if(result==property_checkert::PASS)
    {
      status() << "Termination proved after "
         << unwind << " unwinding(s)" << messaget::eom;
      report_statistics();
      return result;
    }
    else if(result==property_checkert::FAIL)
    {
      status() << "Nonterminating program execution proved after "
         << unwind << " unwinding(s)" << messaget::eom;
      report_statistics();
      return result;
    }
//    else if (result==property_checkert::UNKNOWN)
//    {
//      status() << "Unable to proof nontermination after "
//         << unwind << " unwinding(s)" << messaget::eom;
//    }
  }*/
  second_check_finished=false;

  for(unsigned unwind=1; unwind<=max_unwind; unwind++)
  {
    status() << "Unwinding (k=" << unwind << ")" << messaget::eom;
    ssa_unwinder.unwind_all(unwind);
    if (unwind==51)  //another method check
    {
      result=check_nonterm_linear();
      if(result==property_checkert::PASS)
      {
        status() << "Termination proved after "
           << unwind << " unwinding(s)" << messaget::eom;
        report_statistics();
        return result;
      }
      else if(result==property_checkert::FAIL)
      {
        status() << "Nonterminating program execution proved after "
           << unwind << " unwinding(s)" << messaget::eom;
        report_statistics();
        return result;
      }
    }
    result=summary_checker_baset::check_properties();
    //this is turned - look at it later after getting better result form cover goals
    if(result==property_checkert::PASS)
    {
      status() << "Termination proved after "
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

  //SSA.output_verbose(std::cout);

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
    false,
    options.get_bool_option("show-trace") ||
    options.get_option("graphml-witness")!="" ||
    options.get_option("json-cex")!="");

  property_map.clear();

  exprt::operandst ls_guards;

  loop_map.clear();

  for(local_SSAt::nodest::const_iterator n_it = SSA.nodes.begin();
        n_it != SSA.nodes.end(); n_it++)
  {
    if(n_it->loophead != SSA.nodes.end()) //we've found a loop
    {
      //const source_locationt &location=n_it->loophead->location->source_location;
      irep_idt property_id=irep_idt(n_it->loophead->location->location_number,
                                    0);

      exprt lsguard = SSA.name(SSA.guard_symbol(),
             local_SSAt::LOOP_SELECT, n_it->location);
      ssa_local_unwinder.unwinder_rename(to_symbol_expr(lsguard),*n_it,true);

      const ssa_domaint::phi_nodest &phi_nodes=
        SSA.ssa_analysis[n_it->loophead->location].phi_nodes;

      unsigned loop_idx=
          n_it->loophead->location->location_number;

      if (!loop_map.count(loop_idx)) loop_map[loop_idx]=loop_varst();
      loop_map[loop_idx].source_location=
          n_it->loophead->location->source_location;

      long store_unwinding=SSA.current_unwinding;
      exprt::operandst loop_check_operands;

      symbol_exprt lhguard = SSA.guard_symbol(n_it->loophead->location);
      ssa_local_unwinder.unwinder_rename(lhguard,*n_it,false);

      for (SSA.current_unwinding=1;
           SSA.current_unwinding<=store_unwinding;
           SSA.current_unwinding++)
      {

        exprt::operandst loop_vars;
        loop_vars.push_back(lhguard);

        loop_map[loop_idx].guards.push_back(lhguard);

        for(local_SSAt::objectst::const_iterator
            o_it=SSA.ssa_objects.objects.begin();
            o_it!=SSA.ssa_objects.objects.end();
            o_it++)
        {
          ssa_domaint::phi_nodest::const_iterator p_it=
          phi_nodes.find(o_it->get_identifier());
          if(p_it==phi_nodes.end()) continue; // object not modified in this loop

          symbol_exprt post_var=SSA.name(*o_it, local_SSAt::PHI, n_it->loophead->location);
          ssa_local_unwinder.unwinder_rename(post_var,*n_it->loophead,false);

          symbol_exprt phi_var;
            phi_var=SSA.name(*o_it, local_SSAt::PHI, n_it->loophead->location);
            ssa_local_unwinder.unwinder_rename(phi_var,*n_it->loophead,true);
            loop_vars.push_back(equal_exprt(post_var, phi_var));

            loop_map[loop_idx].vars.push_back(phi_var);
            loop_map[loop_idx].vars.push_back(post_var);
        }

        loop_vars.push_back(ssa_local_unwinder.get_loop_exit_conditions(
                              loop_idx, *n_it->loophead, false));

        loop_map[loop_idx].loop_exits.push_back(loop_vars.back());

        loop_check_operands.push_back(conjunction(loop_vars));

        /*std::cout << "Loop id: " << loop_idx << std::endl;
        std::cout << "guard & vars: " << from_expr(SSA.ns, "",
                                                   conjunction(loop_vars))
                  << std::endl;
        std::cout << "loop. exit cond.: "
                  << from_expr(SSA.ns, "",ssa_local_unwinder
                               .get_loop_exit_conditions(loop_idx,
                                                         *n_it->loophead))
                  << std::endl;*/
      }
      SSA.current_unwinding=store_unwinding;

      property_map[property_id].location=n_it->loophead->location;
      property_map[property_id].result=UNKNOWN;
      cover_goals.goal_map[property_id].conjuncts.push_back(
            disjunction(loop_check_operands));
      ls_guards.push_back(not_exprt(lsguard));

      std::cout << "*************" << " " << loop_idx << " "
                << from_expr(SSA.ns, "", disjunction(loop_check_operands))
                << std::endl;
    }
  }

  /*exprt::operandst assertions;

  const goto_programt &goto_program=SSA.goto_function.body;

  for(goto_programt::instructionst::const_iterator
        i_it=goto_program.instructions.begin();
      i_it!=goto_program.instructions.end();
      i_it++)
  {
    if(!i_it->is_assert())
      continue;

    if(i_it->guard.is_true())
    {
      continue;
    }

    std::list<local_SSAt::nodest::const_iterator> assertion_nodes;
    SSA.find_nodes(i_it, assertion_nodes);

    for(std::list<local_SSAt::nodest::const_iterator>::const_iterator
          n_it=assertion_nodes.begin();
        n_it!=assertion_nodes.end();
        n_it++)
    {
      for(local_SSAt::nodet::assertionst::const_iterator
            a_it=(*n_it)->assertions.begin();
          a_it!=(*n_it)->assertions.end();
          a_it++)
      {
        exprt assertion=*a_it;

        if(simplify)
          assertion=::simplify_expr(assertion, SSA.ns);

        assertions.push_back(not_exprt(assertion));
        loops_collectort::iterator it=loop_map.begin();
        it->second.guards.push_back(assertions.back());
      }
    }
  }*/

  solver << conjunction(ls_guards);
  //solver << disjunction(assertions);

  //std::cout << "++++++++++++" << from_expr(SSA.ns, "", not_exprt(conjunction(assertions))) << std::endl;

  //std::cout << "Formula disjuncts: " << std::endl;
  for(cover_goals_extt::goal_mapt::const_iterator
        it=cover_goals.goal_map.begin();
      it!=cover_goals.goal_map.end();
      it++)
  {
    // Our goal is to falsify a property.
    // The following is TRUE if the conjunction is empty.
    //if (it==cover_goals.goal_map.begin()) continue;
    //std::cout << from_expr(SSA.ns, "", disjunction(it->second.conjuncts)) << std::endl;

    literalt p=solver.convert(disjunction(it->second.conjuncts));
    cover_goals.add(p);
  }

  status() << "Running " << solver.solver->decision_procedure_text() << eom;

  cover_goals();

  // set all non-covered goals to PASS except if we do not try
  //  to cover all goals and we have found a FAIL
  /*if(all_properties || cover_goals.number_covered()==0)
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
  }*/

  /*for (auto & loop : loop_map)
  {
    std::cout << loop.second.source_location << "@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@" << std::endl;
    for (auto guard : loop.second.guards)
    {
      exprt ex = solver.solver->get(guard);
      std::cout << "Solver result for " << from_expr(SSA.ns, "", guard) << " is: ";
      std::cout << from_expr(SSA.ns, "", ex) << std::endl;
    }
    for (auto var : loop.second.vars)
    {
      exprt ex = solver.solver->get(var);
      std::cout << "Solver result for " << from_expr(SSA.ns, "", var) << " is: ";
      std::cout << from_expr(SSA.ns, "", ex) << std::endl;
    }
    for (auto expr : loop.second.loop_exits)
    {
      exprt ex = solver.solver->get(expr);
      std::cout << "Solver result for " << from_expr(SSA.ns, "", expr) << " is: ";
      std::cout << from_expr(SSA.ns, "", ex) << std::endl;
    }
  }

  for(local_SSAt::nodest::const_iterator n_it=SSA.nodes.begin();
        n_it!=SSA.nodes.end(); n_it++)
  {
    if(!n_it->enabling_expr.is_true())
      continue;

    if (!n_it->equalities.empty())
    {
      std::cout << "------------- EQUALITIES --------------" << std::endl;

      for(local_SSAt::nodet::equalitiest::const_iterator
            e_it=n_it->equalities.begin();
          e_it!=n_it->equalities.end();
          e_it++)
      {
        exprt ex = solver.solver->get(*e_it);
        std::cout << "Solver result for " << from_expr(SSA.ns, "", *e_it) << " is: ";
        std::cout << from_expr(SSA.ns, "", ex) << std::endl;
      }
    }

    if (!n_it->constraints.empty())
    {
      std::cout << "------------- CONSTRAINTS --------------" << std::endl;
      for(local_SSAt::nodet::constraintst::const_iterator
            c_it=n_it->constraints.begin();
          c_it!=n_it->constraints.end();
          c_it++)
      {
        exprt ex = solver.solver->get(*c_it);
        std::cout << "Solver result for " << from_expr(SSA.ns, "", *c_it) << " is: ";
        std::cout << from_expr(SSA.ns, "", ex) << std::endl;
      }
    }
  }*/

  solver.pop_context();

  /*std::cout << "** " << cover_goals.number_covered()
          << " of " << cover_goals.size() << " failed ("
          << cover_goals.iterations() << " iterations)" << eom;*/
}

void summary_checker_nontermt::check_properties_linear(
  const ssa_dbt::functionst::const_iterator f_it)
{
  unwindable_local_SSAt &SSA=*f_it->second;

  ssa_local_unwindert &ssa_local_unwinder=ssa_unwinder.get(f_it->first);

  //SSA.output_verbose(std::cout);

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
    false,
    options.get_bool_option("show-trace") ||
    options.get_option("graphml-witness")!="" ||
    options.get_option("json-cex")!="");

  property_map.clear();

  loop_map.clear();

  exprt::operandst ls_guards;
  for(local_SSAt::nodest::const_iterator n_it = SSA.nodes.begin();
        n_it != SSA.nodes.end(); n_it++)
  {
    if(n_it->loophead != SSA.nodes.end()) //we've found a loop
    {
      exprt lsguard = SSA.name(SSA.guard_symbol(),
             local_SSAt::LOOP_SELECT, n_it->location);
      ssa_local_unwinder.unwinder_rename(to_symbol_expr(lsguard),*n_it,true);
      ls_guards.push_back(lsguard);
    }
  }


  int loop_counter=-1;
  for(local_SSAt::nodest::const_iterator n_it = SSA.nodes.begin();
        n_it != SSA.nodes.end(); n_it++)
  {
    //std::cout << "££££££££££££££££" << solver.activation_literals.size() << std::endl;
    if(n_it->loophead != SSA.nodes.end()) //we've found a loop
    {
      loop_counter++; //at the end would not be always incremented(continue;)

      //const source_locationt &location=n_it->loophead->location->source_location;
      irep_idt property_id=irep_idt(n_it->loophead->location->location_number,
                                    0);

      //  TODO: take it from vector of lsguards
      exprt lsguard = SSA.name(SSA.guard_symbol(),
             local_SSAt::LOOP_SELECT, n_it->location);
      ssa_local_unwinder.unwinder_rename(to_symbol_expr(lsguard),*n_it,true);

      const ssa_domaint::phi_nodest &phi_nodes=
        SSA.ssa_analysis[n_it->loophead->location].phi_nodes;

      unsigned loop_idx=
        n_it->loophead->location->location_number;

      if (!loop_map.count(loop_idx)) loop_map[loop_idx]=loop_varst();
      loop_map[loop_idx].source_location=
          n_it->loophead->location->source_location;

      SSA.current_unwinding-=1;
      symbol_exprt lhguard_second=SSA.guard_symbol(n_it->loophead->location);
      ssa_local_unwinder.unwinder_rename(lhguard_second,*n_it,true);
      SSA.current_unwinding+=1;

      symbol_exprt lhguard = SSA.guard_symbol(n_it->loophead->location);
      ssa_local_unwinder.unwinder_rename(lhguard,*n_it,true);

      // linear dependency check

      exprt::operandst first_linearity_check;
      exprt::operandst second_linearity_check;
      exprt::operandst constants_computation;
      exprt::operandst constants;
      exprt::operandst loopback_vars;
      exprt::operandst loop_exit_cond;
      exprt::operandst neg_loop_exit_cond;
      //first_linearity_check.push_back(lhguard);
      //second_linearity_check.push_back(lhguard);

      loop_map[loop_idx].guards.push_back(lhguard);

      property_map[property_id].location=n_it->loophead->location;
      property_map[property_id].result=UNKNOWN;

      unsigned const_number=0;
      for(local_SSAt::objectst::const_iterator
          o_it=SSA.ssa_objects.objects.begin();
          o_it!=SSA.ssa_objects.objects.end();
          o_it++)
      {
        ssa_domaint::phi_nodest::const_iterator p_it=
        phi_nodes.find(o_it->get_identifier());
        if (p_it==phi_nodes.end()) continue; // object not modified in this loop

        //  first linearity check data preparation

        SSA.current_unwinding-=1;
        symbol_exprt phi_var1;
        phi_var1=SSA.name(*o_it, local_SSAt::PHI, n_it->loophead->location);
        ssa_local_unwinder.unwinder_rename(phi_var1,*n_it->loophead,true);
        SSA.current_unwinding+=1;
        symbol_exprt phi_var2;
        phi_var2=SSA.name(*o_it, local_SSAt::PHI, n_it->loophead->location);
        ssa_local_unwinder.unwinder_rename(phi_var2,*n_it->loophead,true);

        //  works only for integers

        if ((phi_var2.type().id()!=ID_unsignedbv) &&
            (phi_var2.type().id()!=ID_signedbv))
        {
          //std::cout << "TYPE: " << phi_var2.type().id() << std::endl;
          first_linearity_check.clear();
          break;
        }

        symbol_exprt constk("const$k", phi_var2.type());
        symbol_exprt const1("const$" + std::to_string(const_number++),
                            phi_var2.type());

        first_linearity_check.push_back(
              equal_exprt(phi_var1, plus_exprt(phi_var2, const1)));

        // get constants data preparation

        constants_computation.push_back(
              equal_exprt(minus_exprt(phi_var1, phi_var2), const1));
        constants.push_back(const1);

        /*std::cout << "phi_var2 - " << from_expr(SSA.ns, "", phi_var2)
                  << " - width: " << to_bitvector_type(phi_var2.type()).
                     get_width() << std::endl;
        std::cout << "phi_var1 - "  << from_expr(SSA.ns, "", phi_var1)
                  << " - width: " << to_bitvector_type(phi_var1.type()).
                     get_width() << std::endl;
        std::cout << "const1 - "  << from_expr(SSA.ns, "", const1)
                  << " - width: " << to_bitvector_type(const1.type()).
                     get_width() << std::endl;*/

        // loopback vars data preparation

        exprt init_expr;
        exprt lb_var;
        for (local_SSAt::nodet::equalitiest::const_iterator e_it=
          n_it->loophead->equalities.begin();
             e_it != n_it->loophead->equalities.end(); e_it++)
        {
          if (e_it->rhs().id() == ID_if &&
              to_symbol_expr(e_it->lhs()).get_identifier()==
              phi_var2.get_identifier())
          {
            const if_exprt &if_expr = to_if_expr(e_it->rhs());
            init_expr=if_expr.false_case();
            lb_var=if_expr.true_case();
            //should already be renamed for inner loops
            break;
          }
        }

        loopback_vars.push_back(lb_var);
        loopback_vars.push_back(init_expr);
        loopback_vars.push_back(constk);

        loop_map[loop_idx].vars.push_back(phi_var1);
        loop_map[loop_idx].vars.push_back(phi_var2);
        loop_map[loop_idx].vars.push_back(init_expr);
        loop_map[loop_idx].vars.push_back(lb_var);
        loop_map[loop_idx].vars.push_back(const1);
        loop_map[loop_idx].vars.push_back(constk);
      }

      if (first_linearity_check.empty())  //nothing to be checked
        continue;

      loop_exit_cond.push_back(lhguard);
      loop_exit_cond.push_back(and_exprt(ssa_local_unwinder.
                                         get_loop_exit_conditions(
                                                            loop_idx,
                                                            *n_it->loophead,
                                                            true),
                                         lhguard_second));
      neg_loop_exit_cond.push_back(lhguard);
      neg_loop_exit_cond.push_back(or_exprt(not_exprt(ssa_local_unwinder.
                                         get_loop_exit_conditions(
                                                            loop_idx,
                                                            *n_it->loophead,
                                                            true)),
                                             not_exprt(lhguard_second)));

      solver.new_context();
      //solver << lhguard_second;
      solver << conjunction(first_linearity_check);
      switch(solver())
      {
      case decision_proceduret::D_UNSATISFIABLE: //
          //std::cout << "£Unsat++++++++++++++++" << std::endl;
          solver.pop_context();
        continue;

      case decision_proceduret::D_SATISFIABLE:
          //std::cout << "£Sat++++++++++++++++" << std::endl;
          for (exprt::operandst::iterator it=first_linearity_check.begin();
               it!=first_linearity_check.end();
               ++it)
          {
            exprt ex=solver.get(it->op1().op1());
            second_linearity_check.push_back(
                  and_exprt(*it, not_exprt(equal_exprt(to_constant_expr(ex),
                                                       it->op1().op1()))));
          }

          solver.pop_context();
        break;

      default:
        error() << "decision procedure has failed" << eom;
        solver.pop_context();
        solver.pop_context();
        return;
      }

      solver.new_context();
      //solver << lhguard_second;
      solver << disjunction(second_linearity_check);
      switch(solver())
      {
      case decision_proceduret::D_UNSATISFIABLE: //
          //std::cout << "£Unsat++++++++++++++++" << std::endl;
          solver.pop_context();
        break;

      case decision_proceduret::D_SATISFIABLE:
          /*std::cout << "£Sat++++++++++++++++" << std::endl;
          for (auto & loop : loop_map)
          {
            std::cout << loop.second.source_location << "@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@" << std::endl;
            for (auto guard : loop.second.guards)
            {
              exprt ex = solver.solver->get(guard);
              std::cout << "Solver result for " << from_expr(SSA.ns, "", guard) << " is: ";
              std::cout << from_expr(SSA.ns, "", ex) << std::endl;
            }
            for (auto var : loop.second.vars)
            {
              exprt ex = solver.solver->get(var);
              std::cout << "Solver result for " << from_expr(SSA.ns, "", var) << " is: ";
              std::cout << from_expr(SSA.ns, "", ex) << std::endl;
            }
            for (auto expr : loop.second.loop_exits)
            {
              exprt ex = solver.solver->get(expr);
              std::cout << "Solver result for " << from_expr(SSA.ns, "", expr) << " is: ";
              std::cout << from_expr(SSA.ns, "", ex) << std::endl;
            }
          }*/
          solver.pop_context();
        continue;

      default:
        error() << "decision procedure has failed" << eom;
        solver.pop_context();
        solver.pop_context();
        return;
      }

      // constants extraction
      exprt::operandst solver_consts;

      solver.new_context();
      solver << conjunction(constants_computation);
      switch(solver())
      {
      case decision_proceduret::D_UNSATISFIABLE: // should never happen
          //std::cout << "£Unsat++++++++++++++++" << std::endl;
          solver.pop_context();
          solver.pop_context();
        return;

      case decision_proceduret::D_SATISFIABLE:
        // mark the goals we got
          //std::cout << "£Sat++++++++++++++++" << std::endl;
          for (auto constant : constants)
          {
            exprt ex = solver.solver->get(constant);
            /*std::cout << "Expr id: " << ex.id() << " val: "
                      << from_expr(SSA.ns, "", ex) << std::endl;*/
            if (ex.type().id()==ID_unsignedbv)
            {
              // if (constant>UINT_MAX/2)?0-constant:constant
              constant_exprt cex=to_constant_expr(ex);
              constant_exprt zero=constant_exprt("0", ex.type());
              constant_exprt cex2=to_constant_expr(
                    simplify_expr(minus_exprt(zero, cex), SSA.ns));
              if_exprt ifex=if_exprt(binary_relation_exprt(
                    cex, ID_gt, cex2), cex2, cex, ex.type());
              ex=simplify_expr(ifex, SSA.ns);
            }
            solver_consts.push_back(to_constant_expr((ex)));
            /*std::cout << "Solver result for "
                      << from_expr(SSA.ns, "", constant) << " is: ";
            std::cout << from_expr(SSA.ns, "", ex) << std::endl;*/
          }
          solver.pop_context();
        break;

      default:
        error() << "decision procedure has failed" << eom;
        solver.pop_context();
        solver.pop_context();
        return;
      }

      // loop exit conditions satisfiable check

      solver.new_context();

      for (unsigned i = 0; i < ls_guards.size(); ++i)
      {
        //std::cout << "Loop counter: " << loop_counter << std::endl;
        if (i != loop_counter)
          solver << not_exprt(ls_guards[i]);
      }

      exprt eq_exprt;
      exprt::operandst::iterator lbv_it=loopback_vars.begin();
      exprt::operandst::iterator slvc_it=solver_consts.begin();
      while (slvc_it!=solver_consts.end())
      {
        //Exists k : xlb == xinit+const*k
        eq_exprt=equal_exprt(*lbv_it, plus_exprt(*(lbv_it+1),
                                mult_exprt(*slvc_it, *(lbv_it+2))));
        solver << eq_exprt;
        loop_map[loop_idx].vars.push_back(eq_exprt);
        ++slvc_it;
        lbv_it+=3;
      }

      solver.new_context();

      solver << conjunction(neg_loop_exit_cond);

      exprt::operandst constraints;
      decision_proceduret::resultt result;
      do {
        exprt::operandst local_constraints;
        switch(result=solver())
        {
        case decision_proceduret::D_UNSATISFIABLE:
            //std::cout << "£Unsat++++++++++++++++" << std::endl;
          break;

        case decision_proceduret::D_SATISFIABLE:
          // mark the goals we got
            //std::cout << "£Sat++++++++++++++++" << std::endl;
            lbv_it=loopback_vars.begin();
            slvc_it=solver_consts.begin();
            while (slvc_it!=solver_consts.end())
            {
              exprt old_xinit = solver.solver->get(*(lbv_it+1));

              //  TODO: make this in different way
              /*std::cout << "Expr id: " << old_xinit.id() << " val: "
                        << from_expr(SSA.ns, "", old_xinit) << std::endl;*/
              if (!from_expr(SSA.ns, "", *slvc_it).compare("0"))
                eq_exprt=equal_exprt(*(lbv_it+1), to_constant_expr(
                                       simplify_expr(old_xinit, SSA.ns)));
              else
                //  Exists xinit % const != old_xinit % const
                eq_exprt=
                    (equal_exprt(mod_exprt(*(lbv_it+1), *slvc_it),
                                 mod_exprt(to_constant_expr(
                                             simplify_expr(old_xinit, SSA.ns)),
                                 *slvc_it)));
              local_constraints.push_back(eq_exprt);
              ++slvc_it;
              lbv_it+=3;
            }
            constraints.push_back(not_exprt(conjunction(local_constraints)));
            solver << not_exprt(conjunction(local_constraints));
          break;

        default:
          error() << "decision procedure has failed" << eom;
          solver.pop_context();
          solver.pop_context();
          solver.pop_context();
          return;
        }
      } while (result!=decision_proceduret::D_UNSATISFIABLE);

      loop_map[loop_idx].vars.push_back(conjunction(constraints));

      solver.pop_context();

      solver << conjunction(loop_exit_cond);
      solver << conjunction(constraints);

      switch(solver())
      {
      case decision_proceduret::D_UNSATISFIABLE:
          //std::cout << "£Unsat++++++++++++++++" << std::endl;
          solver.pop_context();
        break;

      case decision_proceduret::D_SATISFIABLE:
        // found nontermination
          property_map[property_id].result=FAIL;
          /*std::cout << "£Sat++++++++++++++++" << std::endl;
          for (auto & loop : loop_map)
          {
            std::cout << loop.second.source_location << "@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@" << std::endl;
            for (auto guard : loop.second.guards)
            {
              exprt ex = solver.solver->get(guard);
              std::cout << "Solver result for " << from_expr(SSA.ns, "", guard) << " is: ";
              std::cout << from_expr(SSA.ns, "", ex) << std::endl;
            }
            for (auto var : loop.second.vars)
            {
              exprt ex = solver.solver->get(var);
              std::cout << "Solver result for " << from_expr(SSA.ns, "", var) << " is: ";
              std::cout << from_expr(SSA.ns, "", ex) << std::endl;
            }
            for (auto expr : loop.second.loop_exits)
            {
              exprt ex = solver.solver->get(expr);
              std::cout << "Solver result for " << from_expr(SSA.ns, "", expr) << " is: ";
              std::cout << from_expr(SSA.ns, "", ex) << std::endl;
            }
          }*/
          solver.pop_context();
          solver.pop_context();
        return;

      default:
        error() << "decision procedure has failed" << eom;
        solver.pop_context();
        solver.pop_context();
        return;
      }
    }
  }
  solver.pop_context();

  /*std::cout << "** " << cover_goals.number_covered()
          << " of " << cover_goals.size() << " failed ("
          << cover_goals.iterations() << " iterations)" << eom;*/
}

summary_checker_baset::resultt summary_checker_nontermt::check_nonterm_linear()
{
  // analyze all the functions
  for(ssa_dbt::functionst::const_iterator f_it=ssa_db.functions().begin();
      f_it!=ssa_db.functions().end(); f_it++)
  {
    status() << "Checking properties of " << f_it->first << messaget::eom;

#if 0
    // for debugging
    show_ssa_symbols(*f_it->second, std::cerr);
#endif

    check_properties_linear(f_it);
  }

  summary_checker_baset::resultt result=property_checkert::PASS;
  for(property_mapt::const_iterator
        p_it=property_map.begin(); p_it!=property_map.end(); p_it++)
  {
    if(p_it->second.result==FAIL)
      return property_checkert::FAIL;
    if(p_it->second.result==UNKNOWN)
      result=property_checkert::UNKNOWN;
  }

  return result;
}
