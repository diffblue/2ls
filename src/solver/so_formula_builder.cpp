/*******************************************************************\

Module: Second-Order Formula Builder

Author: Peter Schrammel

\*******************************************************************/

#include "so_formula_builder.h"


/*******************************************************************\

Function: so_formula_buildert::predicate_identifier()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

irep_idt so_formula_buildert::predicate_identifier(
    const irep_idt &kind,
    const irep_idt &name,
    const irep_idt &instance)
{
  return id2string(kind)+"#"+id2string(name)+"#"+id2string(instance);
}

/*******************************************************************\

Function: so_formula_buildert::summary()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt so_formula_buildert::summary(const block_ssat &ssa)
{
} 

/*******************************************************************\

Function: so_formula_buildert::invariants()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt so_formula_buildert::invariants(const block_ssat &ssa)
{
} 

/*******************************************************************\

Function: so_formula_buildert::calling_contexts()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt so_formula_buildert::calling_contexts(const block_ssat &ssa)
{
} 

/*******************************************************************\

Function: so_formula_buildert::recsum()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt so_formula_buildert::recsum(const block_ssat &ssa)
{
} 

