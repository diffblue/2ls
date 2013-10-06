/*******************************************************************\

Module: SSA

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_FUNCTION_SSA_H
#define CPROVER_FUNCTION_SSA_H

#include <util/std_expr.h>

#include <goto-programs/goto_functions.h>

#include "ssa_domain.h"

class function_SSAt
{
public:
  typedef goto_functionst::goto_functiont goto_functiont;
  typedef goto_programt::const_targett locationt;

  inline function_SSAt(
    const goto_functiont &_goto_function,
    const namespacet &_ns,
    const std::string &_suffix=""):
    ns(_ns), goto_function(_goto_function), 
    suffix(_suffix)
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
  };
  
  // turns the assertions in the function into constraints
  void assertions_to_constraints();

  // all the SSA nodes  
  typedef std::map<locationt, nodet> nodest;
  nodest nodes;

  // auxiliary functions
  enum kindt { PHI, OUT, LOOP };
  symbol_exprt name(const symbol_exprt &, kindt kind, locationt loc) const;
  symbol_exprt name(const symbol_exprt &, const ssa_domaint::deft &) const;
  symbol_exprt name_input(const symbol_exprt &) const;
  exprt read_rhs(const exprt &, locationt loc) const;
  symbol_exprt read_rhs(const symbol_exprt &, locationt loc) const;
  symbol_exprt read_in(const symbol_exprt &, locationt loc) const;
  exprt read_lhs(const exprt &, locationt loc) const;
  static symbol_exprt guard_symbol();
  symbol_exprt guard_symbol(locationt loc) const
  { return name(guard_symbol(), OUT, loc); }
  bool assigns(const symbol_exprt &, locationt loc) const;

  const namespacet &ns;
  const goto_functiont &goto_function;

  // the objects accessed
  typedef std::set<symbol_exprt> objectst;
  objectst objects;
  
protected:
  ssa_ait ssa_analysis;
  std::string suffix; // an extra suffix  

  // collect all the objects involved
  void collect_objects();
  void collect_objects_rec(const exprt &);

  // build the SSA formulas
  void build_SSA();

  // incoming and outgoing data-flow
  void build_phi_nodes(locationt loc);
  void build_transfer(locationt loc);
  void build_guard(locationt loc);
};

std::list<exprt> & operator <<
  (std::list<exprt> &dest, const function_SSAt &src);

#endif
