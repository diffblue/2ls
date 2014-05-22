/*******************************************************************\

Module: SSA

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_LOCAL_SSA_H
#define CPROVER_LOCAL_SSA_H

#include <util/std_expr.h>

#include <goto-programs/goto_functions.h>

#include "ssa_domain.h"
#include "guard_map.h"
#include "ssa_object.h"

class local_SSAt
{
public:
  typedef goto_functionst::goto_functiont goto_functiont;
  typedef goto_programt::const_targett locationt;

  inline local_SSAt(
    const goto_functiont &_goto_function,
    const namespacet &_ns,
    const std::string &_suffix=""):
    ns(_ns), goto_function(_goto_function), 
    assignments(_goto_function.body, ns),
    guard_map(_goto_function.body),
    ssa_analysis(assignments),
    suffix(_suffix),
    nondet_counter(0)
  {
    build_SSA();
  }
  
  void output(std::ostream &) const;

  // the SSA node for a location
  class nodet
  {
  public:
    typedef std::vector<equal_exprt> equalitiest;
    equalitiest equalities;

    typedef std::vector<exprt> constraintst;
    constraintst constraints;
    
    typedef std::set<locationt> incomingt;
    incomingt incoming;
    
    void output(std::ostream &, const namespacet &) const;

    bool empty() const
    {
      return equalities.empty() && constraints.empty();
    }
  };
  
  // turns the assertions in the function into constraints
  void assertions_to_constraints();

  // all the SSA nodes  
  typedef std::map<locationt, nodet> nodest;
  nodest nodes;

  // auxiliary functions
  enum kindt { PHI, OUT, LOOP_BACK, LOOP_SELECT };
  symbol_exprt name(const ssa_objectt &, kindt kind, locationt loc) const;
  symbol_exprt name(const ssa_objectt &, const ssa_domaint::deft &) const;
  symbol_exprt name_input(const ssa_objectt &) const;
  exprt read_rhs(const exprt &, locationt loc) const;
  exprt read_rhs_rec(const exprt &, locationt loc) const;
  symbol_exprt read_rhs(const ssa_objectt &, locationt loc) const;
  exprt read_node_in(const ssa_objectt &, locationt loc) const;
  exprt read_lhs(const exprt &, locationt loc) const;
  ssa_objectt guard_symbol() const;
  symbol_exprt guard_symbol(locationt loc) const
  { return name(guard_symbol(), OUT, guard_map[loc].guard_source); }
  void assign_rec(const exprt &lhs, const exprt &rhs, locationt loc);
  
  bool has_static_lifetime(const ssa_objectt &) const;
  bool has_static_lifetime(const exprt &) const;

  const namespacet &ns;
  const goto_functiont &goto_function;
  
  typedef assignmentst::objectst objectst;
  assignmentst assignments;
  
protected:
  guard_mapt guard_map;
  ssa_ait ssa_analysis;
  std::string suffix; // an extra suffix
  unsigned nondet_counter;

  // build the SSA formulas
  void build_SSA();

  // incoming and outgoing data-flow
  void build_phi_nodes(locationt loc);
  void build_transfer(locationt loc);
  void build_guard(locationt loc);
  
  exprt same_object(const ssa_objectt &, const ssa_objectt &) const;
};

std::list<exprt> & operator <<
  (std::list<exprt> &dest, const local_SSAt &src);

class decision_proceduret & operator <<
  (class decision_proceduret &dest, const local_SSAt &src);

#endif
