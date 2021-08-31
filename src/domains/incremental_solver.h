/*******************************************************************\

Module: Incremental Solver Interface

Author: Peter Schrammel

\*******************************************************************/

/// \file
/// Incremental Solver Interface

#ifndef CPROVER_2LS_DOMAINS_INCREMENTAL_SOLVER_H
#define CPROVER_2LS_DOMAINS_INCREMENTAL_SOLVER_H

#include <map>
#include <iostream>

#include <solvers/flattening/bv_pointers.h>
#include <solvers/refinement/bv_refinement.h>
#include <solvers/sat/satcheck.h>

#include "util.h"

// #define DISPLAY_FORMULA
// #define NO_ARITH_REFINEMENT
// #define NON_INCREMENTAL // (experimental)

// #define DISPLAY_FORMULA
// #define DEBUG_FORMULA
// #define DEBUG_OUTPUT

class incremental_solvert:public messaget
{
 public:
  typedef std::list<exprt> constraintst;
  typedef std::list<constraintst> contextst;

  explicit incremental_solvert(
    const namespacet &_ns,
    message_handlert &_message_handler,
    bool _arith_refinement=false):
    messaget(_message_handler),
    sat_check(NULL),
    solver(NULL),
    ns(_ns),
    activation_literal_counter(0),
    domain_number(0),
    arith_refinement(_arith_refinement),
    solver_calls(0)
  {
    allocate_solvers(_arith_refinement);
    contexts.push_back(constraintst());
  }

  virtual ~incremental_solvert()
  {
    deallocate_solvers();
  }

  virtual void set_message_handler(message_handlert &handler)
  {
    messaget::set_message_handler(handler);
#if 0
    sat_check->set_message_handler(handler);
    solver->set_message_handler(handler);
#endif
  }

  decision_proceduret::resultt operator()()
  {
    solver_calls++;

#ifdef NON_INCREMENTAL
    deallocate_solvers();
    allocate_solvers(arith_refinement);
    unsigned context_no=0;
    for(const auto &context : contexts)
    {
#ifdef DISPLAY_FORMULA
        std::cerr << "context: " << context_no << std::endl;
#endif
        for(const auto &constraint : context)
      {
#ifdef DISPLAY_FORMULA
        std::cerr << "actual add_to_solver: "
                  << from_expr(ns, "", constraint) << std::endl;
#endif
        *solver << constraint;
      }
    }
#else
#ifdef DEBUG_FORMULA
    bvt whole_formula=formula;
    whole_formula.insert(
      whole_formula.end(),
      activation_literals.begin(),
      activation_literals.end());
    solver->set_assumptions(whole_formula);
#endif
#endif

    return (*solver)();
  }

  exprt get(const exprt& expr) { return solver->get(expr); }
  tvt l_get(literalt l) { return solver->l_get(l); }
  literalt convert(const exprt& expr) { return solver->convert(expr); }

  unsigned get_number_of_solver_calls() { return solver_calls; }

  unsigned next_domain_number() { return domain_number++; }

  static incremental_solvert *allocate(
    const namespacet &_ns,
    message_handlert &_message_handler,
    bool arith_refinement=false)
  {
    return new incremental_solvert(_ns, _message_handler, arith_refinement);
  }

  inline prop_convt & get_solver() { return *solver; }

  propt *sat_check;
  prop_conv_solvert *solver;
  const namespacet &ns;

  void new_context();
  void pop_context();

  // for debugging
  bvt formula;
  void debug_add_to_formula(const exprt &expr);

  // non-incremental solving
  contextst contexts;

 protected:
#ifndef DEBUG
  null_message_handlert null_message_handler;
#endif
  unsigned activation_literal_counter;
  unsigned domain_number; // ids for each domain instance to make symbols unique
  bool arith_refinement;

  // statistics
  unsigned solver_calls;

  void allocate_solvers(bool arith_refinement)
  {
#ifdef DEBUG
    sat_check=new satcheckt(get_message_handler());
#else
    sat_check=new satcheckt(null_message_handler);
#endif
#if 0
    sat_check=new satcheck_minisat_no_simplifiert();
#endif
#ifdef NON_INCREMENTAL
    solver=new bv_pointerst(ns, *sat_check);
#else
    bv_refinementt::infot info;
    info.ns=&ns;
    info.prop=sat_check;
    info.refine_arrays=false;
    info.refine_arithmetic=arith_refinement;

    solver=new bv_refinementt(info);
    solver->set_all_frozen();
#endif
  }

  void deallocate_solvers()
  {
    if(solver!=NULL)
      delete solver;
    if(sat_check!=NULL)
      delete sat_check;
  }
};

static inline incremental_solvert &operator<<(
  incremental_solvert &dest,
  const exprt &src)
{
#ifdef DISPLAY_FORMULA
  if(!dest.activation_literals.empty())
    std::cerr << "add_to_solver(" << !dest.activation_literals.back() << "): "
              << from_expr(dest.ns, "", src) << std::endl;
  else
    std::cerr << "add_to_solver: "
              << from_expr(dest.ns, "", src) << std::endl;
#endif

#ifdef NON_INCREMENTAL
  dest.contexts.back().push_back(src);
#else
#ifndef DEBUG_FORMULA
  *dest.solver << src;
#else
  if(!dest.activation_literals.empty())
  {
    literal_exprt act_lit(!dest.activation_literals.back());
    dest.debug_add_to_formula(or_exprt(src, act_lit));
  }
  else
    dest.debug_add_to_formula(src);
#endif
#endif
  return dest;
}

static inline incremental_solvert &operator<<(
  incremental_solvert &dest,
  const incremental_solvert::constraintst &src)
{
#ifdef NON_INCREMENTAL
  dest.contexts.back().insert(
    dest.contexts.back().begin(), src.begin(), src.end());
#else
  for(const auto &constraint : src)
    {
      dest << constraint;
    }
#endif
  return dest;
}

#endif
