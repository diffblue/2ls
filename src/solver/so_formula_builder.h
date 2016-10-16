/*******************************************************************\

Module: Second-Order Formula Builder

Author: Peter Schrammel

\*******************************************************************/

#ifndef CPROVER_2LS_SO_FORMULA_BUILDER_H
#define CPROVER_2LS_SO_FORMULA_BUILDER_H

#include <ssa/block_ssa.h>
#include <domains/template_generator.h>

class so_formula_buildert
{
public:
  so_formula_buildert(const namespacet &_ns)
    : ns(_ns)
  {
  }

  irep_idt predicate_identifier(
    const irep_idt &kind,
    const irep_idt &name,
    const irep_idt &instance);

  exprt summary(const block_ssat &ssa);
  exprt invariants(const block_ssat &ssa);
  exprt calling_contexts(const block_ssat &ssa);
  exprt recsum(const block_ssat &ssa);

protected:
  const namespacet &ns;
};

#endif
