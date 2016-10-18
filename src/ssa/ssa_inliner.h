/*******************************************************************\

Module: SSA Inliner

Author: Peter Schrammel

\*******************************************************************/

#ifndef CPROVER_2LS_SSA_SSA_INLINER_H
#define CPROVER_2LS_SSA_SSA_INLINER_H

#include <util/message.h>

#include <solver/summary.h>
#include <solver/summary_db.h>

#include "ssa_db.h"
#include "local_ssa.h"

class ssa_inlinert:public messaget
{
public:
  explicit ssa_inlinert(summary_dbt &_summary_db):
    counter(0),
    summary_db(_summary_db)
  {
  }

  void get_summary(
    const local_SSAt &SSA,
    local_SSAt::nodest::const_iterator n_it,
    local_SSAt::nodet::function_callst::const_iterator f_it,
    const summaryt &summary,
    bool forward,
    exprt::operandst &summaries,
    exprt::operandst &bindings);
  void get_summaries(
    const local_SSAt &SSA,
    bool forward,
    exprt::operandst &summaries,
    exprt::operandst &bindings);
  exprt get_summaries(const local_SSAt &SSA);

  void replace(
    local_SSAt &SSA,
    local_SSAt::nodest::iterator node,
    local_SSAt::nodet::function_callst::iterator f_it,
    const local_SSAt::var_sett &cs_globals_in,
    // incoming globals at call site
    const local_SSAt::var_sett &cs_globals_out,
    // outgoing globals at call site
    const summaryt &summary,
    bool forward,
    bool preconditions_as_assertions);

  void replace(
    local_SSAt &SSA,
    bool forward,
    bool preconditions_as_assertions);

  void replace(
    local_SSAt::nodest &nodes,
    local_SSAt::nodest::iterator node,
    local_SSAt::nodet::function_callst::iterator f_it,
    const local_SSAt::var_sett &cs_globals_in,
    // incoming globals at call site
    const local_SSAt::var_sett &cs_globals_out,
    // outgoing globals at call site
    const local_SSAt &function);

  void replace(
    local_SSAt &SSA,
    const ssa_dbt &ssa_db,
    bool recursive=false,
    bool rename=true);

  void havoc(
    local_SSAt::nodet &node,
    local_SSAt::nodet::function_callst::iterator f_it);

  // apply changes to node, must be called after replace and havoc
  void commit_node(local_SSAt::nodest::iterator node);
  bool commit_nodes(
    local_SSAt::nodest &nodes,
    local_SSAt::nodest::iterator n_pos);

  // functions for renaming preconditions to calling context
  void rename_to_caller(
    local_SSAt::nodet::function_callst::const_iterator f_it,
    const local_SSAt::var_listt &params,
    const local_SSAt::var_sett &cs_globals_in,
    const local_SSAt::var_sett &globals_in,
    exprt &expr);
  void rename_to_callee(
    local_SSAt::nodet::function_callst::const_iterator f_it,
    const local_SSAt::var_listt &params,
    const local_SSAt::var_sett &cs_globals_in,
    const local_SSAt::var_sett &globals_in,
    exprt &expr);

  static bool find_corresponding_symbol(
    const symbol_exprt &s,
    const local_SSAt::var_sett &globals,
    symbol_exprt &s_found);

  static bool find_corresponding_dyn_obj(const symbol_exprt &s,
                                         const summaryt &summary,
                                         const function_application_exprt &funapp_expr,
                                         const local_SSAt::nodet &ssa_node,
                                         const namespacet &ns,
                                         symbol_exprt &found_sym);

  static irep_idt get_original_identifier(const symbol_exprt &s);

	static bool is_struct_member(const irep_idt &identifier);

protected:
  unsigned counter;
  summary_dbt &summary_db;

  local_SSAt::nodest new_nodes;
  local_SSAt::nodet::equalitiest new_equs;
  std::set<local_SSAt::nodet::function_callst::iterator> rm_function_calls;

  void replace_globals_in(
    const local_SSAt::var_sett &globals_in,
    const local_SSAt::var_sett &globals);
  void replace_params(
    const local_SSAt::var_listt &params,
    const function_application_exprt &funapp_expr);
  void replace_globals_out(
    const local_SSAt::var_sett &globals_out,
    const local_SSAt::var_sett &cs_globals_in,
    const local_SSAt::var_sett &cs_globals_out);

  exprt get_replace_globals_in(
    const local_SSAt::var_sett &globals_in, 
    const local_SSAt::var_sett &globals);
  exprt get_replace_params(
    const local_SSAt::var_listt &params,
    const function_application_exprt &funapp_expr,
    const local_SSAt::var_sett &globals_in,
    const local_SSAt::var_sett &globals_out,
    const local_SSAt &SSA,
    const local_SSAt::locationt &loc);
  exprt get_replace_globals_out(
    const local_SSAt::var_sett &cs_globals_in,
    const local_SSAt::var_sett &cs_globals_out,
    const summaryt &summary,
    const function_application_exprt &funapp_expr,
    const local_SSAt::nodet &ssa_node,
    const namespacet &ns);

  void rename(exprt &expr);
  void rename(local_SSAt::nodet &node);
};

#endif
