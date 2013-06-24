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
    const namespacet &_ns):ns(_ns)
  {
    build(goto_function);
  }
  
  void output(std::ostream &);
  
  // the guards are conjunctions
  typedef exprt::operandst guardt;
  
  class nodet
  {
  public:
    equal_exprt equality;
    guardt guard;
    goto_programt::const_targett loc;
  };
  
  typedef std::list<nodet> nodest;
  nodest nodes;

protected:
  void build(const goto_functiont &goto_function);
  void output(const nodet &, std::ostream &);

  const namespacet &ns;
  
  typedef std::map<irep_idt, unsigned> ssa_mapt;
  
  exprt rename(const exprt &, ssa_mapt &);
  exprt assign(const exprt &, ssa_mapt &);

};

#endif
