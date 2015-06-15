/*******************************************************************\

Module: Horn-clause Encoding

Author: Daniel Kroening

Date: June 2015

\*******************************************************************/

#include <ostream>

#include <solvers/smt2/smt2_conv.h>

#include "../ssa/local_ssa.h"

#include "horn_encoding.h"

/*******************************************************************\

   Class: horn_encodingt

 Purpose:

\*******************************************************************/

class horn_encodingt
{
public:
  horn_encodingt(
    const goto_modelt &_goto_model,
    std::ostream &_out):
    goto_functions(_goto_model.goto_functions),
    ns(_goto_model.symbol_table),
    out(_out),
    smt2_conv(ns, "", "Horn-clause encoding", "", smt2_convt::Z3, _out)
  {
  }
  
  void operator()();

protected:
  const goto_functionst &goto_functions;
  const namespacet ns;
  std::ostream &out;
  
  smt2_convt smt2_conv;
  
  void translate(const goto_functionst::function_mapt::const_iterator);
};

/*******************************************************************\

Function: horn_encodingt::operator()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void horn_encodingt::operator()()
{
  forall_goto_functions(f_it, goto_functions)
    translate(f_it);
}

/*******************************************************************\

Function: horn_encodingt::translate

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void horn_encodingt::translate(
  const goto_functionst::function_mapt::const_iterator f_it)
{
  if(f_it->second.body.empty())
    return;

  out << "\n"
         ";\n"
         "; Function " << f_it->first << "\n"
         ";\n";

  local_SSAt local_SSA(f_it->second, ns, "");

  const goto_programt &body=f_it->second.body;
  
  for(goto_programt::instructionst::const_iterator
      loc=body.instructions.begin();
      loc!=body.instructions.end();
      loc++)
  {
    const local_SSAt::nodet &node=local_SSA[loc];

    out << "; PC " << loc->location_number
        << " " << loc->source_location << '\n';

    #if 0
    for(local_SSAt::nodet::constraintst::const_iterator
        it=node.constraints.begin();
        it!=node.constraints.end();
        it++)
    {
      smt2_conv.set_to(*it, true);
    }
    #endif

    for(local_SSAt::nodet::equalitiest::const_iterator
        it=node.equalities.begin();
        it!=node.equalities.end();
        it++)
    {
      smt2_conv.set_to(*it, true);
    }

    out << '\n';
  }
}

/*******************************************************************\

Function: horn_encoding

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void horn_encoding(
  const goto_modelt &goto_model,
  std::ostream &out)
{
  horn_encodingt(goto_model, out)();
}
