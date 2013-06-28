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
  };
  
  typedef std::map<locationt, nodet> nodest;
  nodest nodes;

  enum kindt { PHI, OUT };
  symbol_exprt name(const symbol_exprt &, kindt kind, bool prime, locationt loc) const;
  exprt read(const exprt &, locationt loc) const;
  static symbol_exprt guard_symbol();
  bool assigns(const symbol_exprt &, locationt loc) const;

protected:
  const namespacet &ns;
  const goto_functiont &goto_function;
  static_analysist<ssa_domaint> ssa_analysis;
  std::string suffix; // an extra suffix  

  void output(const nodet &, std::ostream &) const;
  
  // collect all the objects involved
  void collect_objects();
  void collect_objects(const exprt &);

  typedef std::set<symbol_exprt> objectst;
  objectst objects; 

  // build the SSA formulas
  void build_SSA();


  // incoming and outgoing data-flow
  void build_phi_nodes(locationt loc);
  void build_transfer(locationt loc);
  void build_guard(locationt loc);
  
  // final phase, optimization
  void optimize();
  static void get_exprs(const exprt &, std::set<exprt> &);
};

#endif
