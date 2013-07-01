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
    ssa_analysis(_ns),
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
    exprt guard;
    
    typedef std::set<locationt> incomingt;
    incomingt incoming;
    
    void output(std::ostream &, const namespacet &) const;
  };

  // all the SSA nodes  
  typedef std::map<locationt, nodet> nodest;
  nodest nodes;

  // auxiliary functions
  enum kindt { PHI, OUT, LOOP };
  symbol_exprt name(const symbol_exprt &, kindt kind, locationt loc) const;
  exprt read(const exprt &, locationt loc) const;
  symbol_exprt read(const symbol_exprt &, locationt loc) const;
  symbol_exprt read_in(const symbol_exprt &, locationt loc) const;
  static symbol_exprt guard_symbol();
  bool assigns(const symbol_exprt &, locationt loc) const;

  const namespacet &ns;
  const goto_functiont &goto_function;

  typedef std::set<symbol_exprt> objectst;
  objectst objects;
  
protected:
  static_analysist<ssa_domaint> ssa_analysis;
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

class decision_proceduret & operator <<
  (decision_proceduret &dest, const function_SSAt &src);

#endif
