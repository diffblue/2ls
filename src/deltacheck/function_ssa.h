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

  inline function_SSAt(
    const goto_functiont &goto_function,
    const namespacet &_ns,
    const std::string &_suffix):ns(_ns), suffix(_suffix)
  {
    build_SSA(goto_function);
  }
  
  inline function_SSAt(
    const goto_functiont &goto_function,
    const namespacet &_ns):ns(_ns)
  {
    build_SSA(goto_function);
  }
  
  void output(std::ostream &);

  // the SSA node  
  class nodet
  {
  public:
    equal_exprt equality;
    exprt guard;
    goto_programt::const_targett loc;
  };
  
  typedef std::list<nodet> nodest;
  nodest nodes;

protected:
  const namespacet &ns;
  std::string suffix; // an extra suffix  

  void output(const nodet &, std::ostream &);
  
  // build the SSA formulas
  void build_SSA(const goto_functiont &goto_function);

  // maps identifier to SSA index
  typedef std::map<irep_idt, unsigned> ssa_mapt;
  ssa_mapt ssa_map;
  
  exprt rename(const exprt &);
  exprt assign(const exprt &);

  symbol_exprt guard_symbol();
};

#endif
