/*******************************************************************\

Module: Delta Checking

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <analyses/goto_check.h>

#include "solver.h"
#include "function_delta.h"

class function_deltat:public messaget
{
public:
  explicit function_deltat(
    std::ostream &_out):out(_out), ns(symbol_table), solver(ns)
  {
  }

  void operator()(
    const irep_idt &id,
    const goto_functionst::goto_functiont &f1,
    const goto_functionst::goto_functiont &f2);
  
protected:
  std::ostream &out;
  symbol_tablet symbol_table;
  namespacet ns;
  solvert solver;
  
  exprt rename_rhs(const exprt &src, goto_programt::const_targett t, unsigned v);
  exprt rename_lhs(const exprt &src, goto_programt::const_targett t, unsigned v);
  
  void encode(const goto_functionst::goto_functiont &goto_function, unsigned v);
};

/*******************************************************************\

Function: function_deltat::encode

  Inputs:

 Outputs:

 Purpose: builds data-flow equations

\*******************************************************************/

void function_deltat::encode(
  const goto_functionst::goto_functiont &f, unsigned v)
{
  const goto_programt &body=f.body;

  forall_goto_program_instructions(i_it, body)
  {
    const goto_programt::instructiont &instruction=*i_it;
    
    if(instruction.is_goto())
    {
      // 'true' branch
      exprt guard_true=rename_rhs(instruction.guard, i_it, v);
      
      // 'false' branch
      exprt guard_false=rename_rhs(gen_not(instruction.guard), i_it, v);
    }
    else if(instruction.is_assert())
    {
    }
    else if(instruction.is_assume())
    {
    }
    else
    {
      // treat like 'skip'
    }
  }
}

/*******************************************************************\

Function: function_deltat::operator()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void function_deltat::operator()(
  const irep_idt &id,
  const goto_functionst::goto_functiont &f1,
  const goto_functionst::goto_functiont &f2)
{
  if(!f2.body.has_assertion())
  {
    status("New version has no properties");
    return;
  }

  out << "<h2>Function " << id << "</h2>\n";

  // encode both programs
  encode(f1, 1);
  encode(f2, 2);
}

/*******************************************************************\

Function: function_delta

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void function_delta(
  const irep_idt &id,
  const goto_functionst::goto_functiont &f1,
  const goto_functionst::goto_functiont &f2,
  std::ostream &out,
  message_handlert &message_handler)
{
  function_deltat function_delta(out);
  function_delta.set_message_handler(message_handler);
  function_delta(id, f1, f2);
}

