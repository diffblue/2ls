/*******************************************************************\

Module: Second-Order Formula Builder

Author: Peter Schrammel

\*******************************************************************/

#ifndef CPROVER_2LS_SO_FORMULA_BUILDER_H
#define CPROVER_2LS_SO_FORMULA_BUILDER_H

#include <ssa/block_ssa.h>
#include <domains/template_generator.h>

#include "predicate.h"
#include "so_formula.h"

class so_formula_buildert
{
public:
  so_formula_buildert(const namespacet &_ns)
    : ns(_ns)
  {
  }

  predicate_symbol_exprt make_pre(const block_ssat &block);
  predicate_symbol_exprt make_post(const block_ssat &block);
  predicate_symbol_exprt make_sum(const block_ssat &block);
//  predicate_symbolst make_invs(const block_ssat &block);

  exprt &make_preamble(const predicate_symbol_sett &symbols, so_formulat &expr);

  function_application_exprt make_block(const block_ssat &block);
  predicate_application_exprt apply(
    const predicate_symbol_exprt &symbol,
    const exprt::operandst &arguments);
  predicate_application_exprt apply(
    const predicate_symbol_exprt &symbol,
    const block_ssat::varst &arguments);
  void add_vars(exprt::operandst &v, const block_ssat::varst &vars);

  so_formulat summary(const block_ssat &block);
  so_formulat invariants(const block_ssat &block);
  so_formulat calling_contexts(const block_ssat &block);
  so_formulat recsum(const block_ssat &block);

  irep_idt predicate_identifier(
    std::string kind,
    irep_idt name,
    std::string instance="");

protected:
  const namespacet &ns;
};

#endif
