/*******************************************************************\

Module: Signature of a Function

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "../ssa/local_ssa.h"
#include "function_signature.h"

/*******************************************************************\

Function: update_function_signature

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void update_function_signature(
  const local_SSAt &SSA,
  class jsont &dest)
{
  jsont &j_signature=dest["signature"];
  jsont &j_reads=j_signature["reads"];
  jsont &j_modifies=j_signature["modifies"];

  j_signature.kind=jsont::J_OBJECT;
  j_reads=jsont::json_array();
  j_modifies=jsont::json_array();
  
  std::set<irep_idt> modifies;
  std::set<irep_idt> reads;

  for(assignmentst::assignment_mapt::const_iterator
      a_it=SSA.assignments.assignment_map.begin();
      a_it!=SSA.assignments.assignment_map.end();
      a_it++)
  {
    for(assignmentst::objectst::const_iterator
        o_it=a_it->second.begin();
        o_it!=a_it->second.end();
        o_it++)
    {
      modifies.insert(o_it->get_identifier());
    }
  }

  for(ssa_objectst::objectst::const_iterator
      o_it=SSA.ssa_objects.objects.begin();
      o_it!=SSA.ssa_objects.objects.end();
      o_it++)
  {
    reads.insert(o_it->get_identifier());
  }

  for(std::set<irep_idt>::const_iterator it=reads.begin();
      it!=reads.end();
      it++)
  {
    j_reads.array.push_back(jsont::json_string(id2string(*it)));
  }

  for(std::set<irep_idt>::const_iterator it=modifies.begin();
      it!=modifies.end();
      it++)
  {
    j_modifies.array.push_back(jsont::json_string(id2string(*it)));
  }

}

