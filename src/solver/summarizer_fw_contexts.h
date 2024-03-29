/*******************************************************************\

Module: Summarizer for Forward Analysis with Calling Context output

Author: Peter Schrammel

\*******************************************************************/

/// \file
/// Summarizer for Forward Analysis with Calling Context output

#ifndef CPROVER_2LS_SOLVER_SUMMARIZER_FW_CONTEXTS_H
#define CPROVER_2LS_SOLVER_SUMMARIZER_FW_CONTEXTS_H

#include <util/message.h>
#include <util/options.h>
#include <util/ui_message.h>

#include <ssa/ssa_inliner.h>
#include <ssa/unwinder.h>
#include <ssa/local_ssa.h>
#include <ssa/ssa_db.h>

#include "summarizer_fw.h"


class summarizer_fw_contextst:public summarizer_fwt
{
public:
  explicit summarizer_fw_contextst(
    optionst &_options,
    summary_dbt &_summary_db,
    ssa_dbt &_ssa_db,
    std::unique_ptr<unwindert> &_ssa_unwinder,
    ssa_inlinert &_ssa_inliner):
    summarizer_fwt(_options, _summary_db, _ssa_db, _ssa_unwinder, _ssa_inliner),
    ui(ui_message_handlert::uit::PLAIN)
  {
    if(_options.get_bool_option("xml-ui"))
      ui=ui_message_handlert::uit::XML_UI;

    optionst::value_listt _excluded_functions=
      _options.get_list_option("do-not-analyze-functions");
    excluded_functions.insert(
      _excluded_functions.begin(), _excluded_functions.end());
  }

  virtual void summarize();

 protected:
  ui_message_handlert::uit ui; // use gui format
  std::set<irep_idt> excluded_functions;

  virtual void inline_summaries(
    const function_namet &function_name,
    local_SSAt &SSA,
    const exprt &precondition,
    bool context_sensitive);
};

#endif
