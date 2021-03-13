/*******************************************************************\

Module: Summarizer for Nontermination Bit-level analysis

Author: Stefan Marticek

\*******************************************************************/

/// \file
/// Summarizer for Nontermination Bit-level analysis

#include "summary_checker_nonterm.h"

#include <util/simplify_expr.h>
#include <util/prefix.h>

#include <ssa/simplify_ssa.h>
#include <2ls/show.h>

#include <limits>

property_checkert::resultt summary_checker_nontermt::operator()(
  const goto_modelt &goto_model)
{
  SSA_functions(goto_model, goto_model.symbol_table);

  ssa_unwinder.init(false, true);

  property_checkert::resultt result=property_checkert::resultt::UNKNOWN;
  unsigned max_unwind=options.get_unsigned_int_option("unwind");
  status() << "Max-unwind is " << max_unwind << eom;
  ssa_unwinder.init_localunwinders();

  for(unsigned unwind=1; unwind<=max_unwind; unwind++)
  {
    status() << "Unwinding (k=" << unwind << ")" << messaget::eom;
    ssa_unwinder.unwind_all(unwind);
    if(unwind==51)  // use a different nontermination technique
    {
      result=check_nonterm_linear();
      if(result==property_checkert::resultt::PASS)
      {
        status() << "Termination proved after "
           << unwind << " unwinding(s)" << messaget::eom;
        report_statistics();
        return result;
      }
      else if(result==property_checkert::resultt::FAIL)
      {
        status() << "Nonterminating program execution proved after "
           << unwind << " unwinding(s)" << messaget::eom;
        report_statistics();
        return result;
      }
    }
    result=summary_checker_baset::check_properties();
    if(result==property_checkert::resultt::PASS)
    {
      status() << "Termination proved after "
         << unwind << " unwinding(s)" << messaget::eom;
      break;
    }
    else if(result==property_checkert::resultt::FAIL)
    {
      status() << "Nonterminating program execution proved after "
         << unwind << " unwinding(s)" << messaget::eom;
      break;
    }
  }

  report_statistics();
  return result;
}

/// checks the property loop instead of assertion
void summary_checker_nontermt::check_properties(
  const ssa_dbt::functionst::const_iterator f_it)
{
  unwindable_local_SSAt &SSA=*f_it->second;

  ssa_local_unwindert &ssa_local_unwinder=ssa_unwinder.get(f_it->first);

#if 0
  SSA.output_verbose(std::cout);
#endif

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
    SSA,
    solver,
    loophead_selects,
    property_map,
    false,
    false,
    options.get_bool_option("trace") ||
    options.get_option("graphml-witness")!="" ||
    options.get_option("json-cex")!="");

  property_map.clear();

  exprt::operandst ls_guards;

  for(local_SSAt::nodest::const_iterator n_it=SSA.nodes.begin();
        n_it!=SSA.nodes.end(); n_it++)
  {
    if(n_it->loophead!=SSA.nodes.end()) // we've found a loop
    {
      irep_idt property_id(
        id2string(n_it->location->function)+"."+
        std::to_string(n_it->location->loop_number)+".term");

      exprt lsguard=
        SSA.name(SSA.guard_symbol(), local_SSAt::LOOP_SELECT, n_it->location);
      ssa_local_unwinder.unwinder_rename(to_symbol_expr(lsguard), *n_it, true);

      const ssa_domaint::phi_nodest &phi_nodes=
        SSA.ssa_analysis[n_it->loophead->location].phi_nodes;

      long store_unwinding=SSA.current_unwinding;
      exprt::operandst loop_check_operands;

      symbol_exprt lhguard=SSA.guard_symbol(n_it->loophead->location);
      ssa_local_unwinder.unwinder_rename(lhguard, *n_it, false);

      for(SSA.current_unwinding=1;
          SSA.current_unwinding<=store_unwinding;
          SSA.current_unwinding++)
      {
        exprt::operandst loop_vars;
        loop_vars.push_back(lhguard);

        for(local_SSAt::objectst::const_iterator
            o_it=SSA.ssa_objects.objects.begin();
            o_it!=SSA.ssa_objects.objects.end();
            o_it++)
        {
          ssa_domaint::phi_nodest::const_iterator p_it=
          phi_nodes.find(o_it->get_identifier());
          if(p_it==phi_nodes.end())
            continue; // object not modified in this loop

          symbol_exprt post_var=
            SSA.name(*o_it, local_SSAt::PHI, n_it->loophead->location);
          ssa_local_unwinder.unwinder_rename(post_var, *n_it->loophead, false);

          symbol_exprt phi_var;
          phi_var=SSA.name(*o_it, local_SSAt::PHI, n_it->loophead->location);
          ssa_local_unwinder.unwinder_rename(phi_var, *n_it->loophead, true);
          loop_vars.push_back(equal_exprt(post_var, phi_var));
        }

        loop_check_operands.push_back(conjunction(loop_vars));
      }
      SSA.current_unwinding=store_unwinding;

      property_map[property_id].location=n_it->loophead->location;
      property_map[property_id].result=property_checkert::resultt::UNKNOWN;
      cover_goals.goal_map[property_id].conjuncts.push_back(
        disjunction(loop_check_operands));
      ls_guards.push_back(not_exprt(lsguard));
    }
  }

  solver << conjunction(ls_guards);

  for(cover_goals_extt::goal_mapt::const_iterator
        it=cover_goals.goal_map.begin();
      it!=cover_goals.goal_map.end();
      it++)
  {
    literalt p=solver.convert(disjunction(it->second.conjuncts));
    cover_goals.add(p);
  }

  status() << "Running " << solver.solver->decision_procedure_text()
           << messaget::eom;

  cover_goals();

  solver.pop_context();

  status() << "** " << cover_goals.number_covered()
           << " of " << cover_goals.size() << " failed ("
           << cover_goals.iterations() << " iterations)"
           << messaget::eom;
}

/// searching for periodical recurrence set
void summary_checker_nontermt::check_properties_linear(
  const ssa_dbt::functionst::const_iterator f_it)
{
  unwindable_local_SSAt &SSA=*f_it->second;

  ssa_local_unwindert &ssa_local_unwinder=ssa_unwinder.get(f_it->first);

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

  property_map.clear();

  exprt::operandst ls_guards;
  for(local_SSAt::nodest::const_iterator n_it=SSA.nodes.begin();
      n_it!=SSA.nodes.end(); n_it++)
  {
    if(n_it->loophead!=SSA.nodes.end()) // we've found a loop
    {
      exprt lsguard=
        SSA.name(SSA.guard_symbol(), local_SSAt::LOOP_SELECT, n_it->location);
      ssa_local_unwinder.unwinder_rename(to_symbol_expr(lsguard), *n_it, true);
      ls_guards.push_back(lsguard);
    }
  }

  unsigned loop_counter=std::numeric_limits<unsigned>::max();
  for(local_SSAt::nodest::const_iterator n_it=SSA.nodes.begin();
      n_it!=SSA.nodes.end(); n_it++)
  {
    if(n_it->loophead!=SSA.nodes.end()) // we've found a loop
    {
      // we use continues further, therefore we put incrementation here
      loop_counter++;

      irep_idt property_id(
        id2string(n_it->location->function)+"."+
        std::to_string(n_it->location->loop_number)+".term");

      const ssa_domaint::phi_nodest &phi_nodes=
        SSA.ssa_analysis[n_it->loophead->location].phi_nodes;

      SSA.current_unwinding-=1;
      symbol_exprt lhguard_second=SSA.guard_symbol(n_it->loophead->location);
      ssa_local_unwinder.unwinder_rename(lhguard_second, *n_it, true);
      SSA.current_unwinding+=1;

      symbol_exprt lhguard=SSA.guard_symbol(n_it->loophead->location);
      ssa_local_unwinder.unwinder_rename(lhguard, *n_it, true);

      exprt::operandst first_linearity_check;
      exprt::operandst second_linearity_check;
      exprt::operandst constants_computation;
      exprt::operandst constants;
      exprt::operandst loopback_vars;
      exprt::operandst loop_exit_cond;
      exprt::operandst neg_loop_exit_cond;

      property_map[property_id].location=n_it->loophead->location;
      property_map[property_id].result=property_checkert::resultt::UNKNOWN;

      unsigned const_number=0;
      for(local_SSAt::objectst::const_iterator
          o_it=SSA.ssa_objects.objects.begin();
          o_it!=SSA.ssa_objects.objects.end();
          o_it++)
      {
        ssa_domaint::phi_nodest::const_iterator p_it=
        phi_nodes.find(o_it->get_identifier());
        if(p_it==phi_nodes.end())
          continue; // object not modified in this loop

        // first linearity check data preparation

        SSA.current_unwinding-=1;
        symbol_exprt phi_var1;
        phi_var1=SSA.name(*o_it, local_SSAt::PHI, n_it->loophead->location);
        ssa_local_unwinder.unwinder_rename(phi_var1, *n_it->loophead, true);
        SSA.current_unwinding+=1;
        symbol_exprt phi_var2;
        phi_var2=SSA.name(*o_it, local_SSAt::PHI, n_it->loophead->location);
        ssa_local_unwinder.unwinder_rename(phi_var2, *n_it->loophead, true);

        // works only for bitvectors

        if((phi_var2.type().id()!=ID_unsignedbv) &&
           (phi_var2.type().id()!=ID_signedbv))
        {
          first_linearity_check.clear();
          break;
        }

        // x_k = x_0 + C*k, const$k - k, const$i - C
        symbol_exprt constk("const$k", phi_var2.type());
        symbol_exprt const1(
          "const$"+std::to_string(const_number++), phi_var2.type());

        first_linearity_check.push_back(
          equal_exprt(
            phi_var1,
            plus_exprt(
              phi_var2,
              const1)));

        // get constants data preparation

        constants_computation.push_back(
          equal_exprt(
            minus_exprt(phi_var1, phi_var2),
            const1));
        constants.push_back(const1);

        // loopback vars data preparation

        exprt init_expr;
        exprt lb_var;
        for(local_SSAt::nodet::equalitiest::const_iterator e_it=
              n_it->loophead->equalities.begin();
            e_it!=n_it->loophead->equalities.end(); e_it++)
        {
          if(e_it->rhs().id()==ID_if &&
             to_symbol_expr(e_it->lhs()).get_identifier()==
             phi_var2.get_identifier())
          {
            const if_exprt &if_expr=to_if_expr(e_it->rhs());
            init_expr=if_expr.false_case();
            lb_var=if_expr.true_case();
            // should already be renamed for inner loops
            break;
          }
        }

        loopback_vars.push_back(lb_var);
        loopback_vars.push_back(init_expr);
        loopback_vars.push_back(constk);
      }

      if(first_linearity_check.empty()) // nothing to be checked
        continue;

      neg_loop_exit_cond.push_back(lhguard);
      neg_loop_exit_cond.push_back(not_exprt(lhguard_second));
      loop_exit_cond.push_back(lhguard);

      solver.new_context();
      solver << conjunction(first_linearity_check);
      switch(solver())
      {
      case decision_proceduret::resultt::D_UNSATISFIABLE:
          solver.pop_context();
        continue;

      case decision_proceduret::resultt::D_SATISFIABLE:
          for(exprt::operandst::iterator it=first_linearity_check.begin();
              it!=first_linearity_check.end();
              ++it)
          {
            exprt ex=solver.get(it->op1().op1());
            second_linearity_check.push_back(
              and_exprt(
                *it,
                not_exprt(equal_exprt(to_constant_expr(ex), it->op1().op1()))));
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
      solver << disjunction(second_linearity_check);
      switch(solver())
      {
      case decision_proceduret::resultt::D_UNSATISFIABLE:
          solver.pop_context();
        break;

      case decision_proceduret::resultt::D_SATISFIABLE:
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
      case decision_proceduret::resultt::D_UNSATISFIABLE: // should never happen
          solver.pop_context();
          solver.pop_context();
        return;

      case decision_proceduret::resultt::D_SATISFIABLE:
          for(auto constant : constants)
          {
            exprt ex=solver.solver->get(constant);
            if(ex.type().id()==ID_unsignedbv)
            {
              // if (constant>UINT_MAX/2)?0-constant:constant
              constant_exprt cex=to_constant_expr(ex);
              constant_exprt zero=constant_exprt("0", ex.type());
              constant_exprt cex2=
                to_constant_expr(simplify_expr(minus_exprt(zero, cex), SSA.ns));
              if_exprt ifex=if_exprt(
                binary_relation_exprt(cex, ID_gt, cex2),
                cex2,
                cex,
                ex.type());
              ex=simplify_expr(ifex, SSA.ns);
            }
            solver_consts.push_back(to_constant_expr((ex)));
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

      for(unsigned i=0; i<ls_guards.size(); ++i)
      {
        if(i!=loop_counter)
          solver << not_exprt(ls_guards[i]);
      }

      exprt eq_expr;
      exprt::operandst::iterator lbv_it=loopback_vars.begin();
      exprt::operandst::iterator slvc_it=solver_consts.begin();
      while(slvc_it!=solver_consts.end())
      {
        // Exists k : xlb == xinit+const*k
        eq_expr=equal_exprt(
          *lbv_it,
          plus_exprt(*(lbv_it+1), mult_exprt(*slvc_it, *(lbv_it+2))));
        solver << eq_expr;
        ++slvc_it;
        lbv_it+=3;
      }

      solver.new_context();

      solver << conjunction(neg_loop_exit_cond);

      exprt::operandst constraints;
      decision_proceduret::resultt result;
      do
      {
        exprt::operandst local_constraints;
        switch(result=solver())
        {
        case decision_proceduret::resultt::D_UNSATISFIABLE:
          break;

        case decision_proceduret::resultt::D_SATISFIABLE:
            lbv_it=loopback_vars.begin();
            slvc_it=solver_consts.begin();
            while(slvc_it!=solver_consts.end())
            {
              exprt old_xinit=solver.solver->get(*(lbv_it+1));

              // TODO: make this in different way
              if(!from_expr(SSA.ns, "", *slvc_it).compare("0"))
              {
                eq_expr=equal_exprt(
                  *(lbv_it+1),
                  to_constant_expr(
                    simplify_expr(
                      old_xinit,
                      SSA.ns)));
              }
              else
              {
                // Exists xinit % const != old_xinit % const
                eq_expr=equal_exprt(
                  mod_exprt(*(lbv_it+1), *slvc_it),
                  mod_exprt(
                    to_constant_expr(simplify_expr(old_xinit, SSA.ns)),
                    *slvc_it));
              }
              local_constraints.push_back(eq_expr);
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
      }
      while(result!=decision_proceduret::resultt::D_UNSATISFIABLE);

      solver.pop_context();

      solver << conjunction(loop_exit_cond);
      solver << conjunction(constraints);

      switch(solver())
      {
      case decision_proceduret::resultt::D_UNSATISFIABLE:
          solver.pop_context();
        break;

      case decision_proceduret::resultt::D_SATISFIABLE:
        // found nontermination
          property_map[property_id].result=property_checkert::resultt::FAIL;
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
}

summary_checker_baset::resultt summary_checker_nontermt::check_nonterm_linear()
{
  // analyze all the functions
  for(ssa_dbt::functionst::const_iterator f_it=ssa_db.functions().begin();
      f_it!=ssa_db.functions().end(); f_it++)
  {
    status() << "Checking properties of " << f_it->first << messaget::eom;

    check_properties_linear(f_it);
  }

  summary_checker_baset::resultt result=property_checkert::resultt::PASS;
  for(property_mapt::const_iterator
        p_it=property_map.begin(); p_it!=property_map.end(); p_it++)
  {
    if(p_it->second.result==property_checkert::resultt::FAIL)
      return property_checkert::resultt::FAIL;
    if(p_it->second.result==property_checkert::resultt::UNKNOWN)
      result=property_checkert::resultt::UNKNOWN;
  }

  return result;
}
