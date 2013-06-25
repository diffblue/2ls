/*******************************************************************\

Module: SSA

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_FUNCTION_SSA_H
#define CPROVER_FUNCTION_SSA_H

#include <util/std_expr.h>

#include <goto-programs/goto_functions.h>

class function_SSAt
{
public:
  typedef goto_functionst::goto_functiont goto_functiont;
  typedef goto_programt::const_targett locationt;

  inline function_SSAt(
    const goto_functiont &_goto_function,
    const namespacet &_ns,
    const std::string &_suffix):
    ns(_ns), goto_function(_goto_function), suffix(_suffix)
  {
    build_SSA();
  }
  
  inline function_SSAt(
    const goto_functiont &_goto_function,
    const namespacet &_ns):
    ns(_ns), goto_function(_goto_function)
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

protected:
  const namespacet &ns;
  const goto_functiont &goto_function;
  std::string suffix; // an extra suffix  

  void output(const nodet &, std::ostream &) const;
  
  // collect all the objects involved
  void collect_objects();
  void collect_objects(const exprt &);

  typedef std::set<symbol_exprt> objectst;
  objectst objects; 

  // build the SSA formulas
  void build_SSA();

  enum kindt { IN, OUT };
  symbol_exprt name(const symbol_exprt &, kindt kind, locationt loc);
  exprt rename(const exprt &, kindt kind, locationt loc);
  symbol_exprt guard();

  // incoming and outgoing data-flow
  void build_incoming();
  void build_outgoing();
  
  // final phase, optimization
  void optimize();
  static void get_exprs(const exprt &, std::set<exprt> &);
};

#endif
