/*******************************************************************\

Module: Summarization

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cuddObj.hh>

#include <numbering.h>

#include "transformer.h"
#include "collect_symbols.h"

class transformert
{
public:
  typedef numbering<irep_idt> varst;
  varst vars;
  
  class statet
  {
  };

  typedef std::map<goto_programt::const_targett, statet> state_mapt;
  state_mapt state_map;
  
  transformert(
    const namespacet &_ns,
    const goto_functionst &_goto_functions):
    ns(_ns),
    goto_functions(_goto_functions),
    mgr(0, 0)
  {
  }
  
  void operator() (const goto_functionst::goto_functiont &);
  
  void output(std::ostream &out) const;
  
protected:
  const namespacet &ns;
  const goto_functionst &goto_functions;
  
  Cudd mgr;
};

/*******************************************************************\

Function: transformert::operator()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void transformert::operator()(const goto_functionst::goto_functiont &goto_function)
{
  #if 0
  find_symbols_sett symbols;
  collect_symbols(goto_function, symbols);

  for(find_symbols_sett::const_iterator
      s_it=symbols.begin();
      s_it!=symbols.end();
      s_it++)
    vars.number(*s_it);

  forall_goto_instructions(i_it, goto_function.goto_program)
    state_map[i_it];
  #endif
}

/*******************************************************************\

Function: transformert::output

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void transformert::output(std::ostream &out) const
{
}

/*******************************************************************\

Function: transformer

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void transformer(
  const namespacet &ns, 
  const goto_functionst &goto_functions,
  const goto_functionst::goto_functiont &goto_function,
  std::ostream &out)
{
  transformert transformer(ns, goto_functions);
  
  transformer(goto_function);
  
  transformer.output(out);
}
