/*******************************************************************\

Module: SSA CFA extension for GraphML output

Author: Peter Schrammel

\*******************************************************************/

/// \file
/// SSA CFA extension for GraphML output

#ifndef CPROVER_2LS_2LS_GRAPHML_WITNESS_EXT_H
#define CPROVER_2LS_2LS_GRAPHML_WITNESS_EXT_H

#include <util/std_expr.h>

#include <goto-programs/graphml_witness.h>

#include "dynamic_cfg.h"
#include "summary_checker_base.h"


class graphml_witness_extt:public graphml_witnesst
{
public:
  explicit graphml_witness_extt(const namespacet &ns):
    graphml_witnesst(ns) {}

  // correctness witness
  void operator()(const summary_checker_baset &summary_checker);

protected:
  graphmlt::node_indext add_node(
    std::map<unsigned,
    unsigned> &loc_to_node,
    goto_programt::const_targett it);

  void add_edge(
    const graphmlt::node_indext &from,
    const dynamic_cfg_nodet &from_cfg_node,
    const graphmlt::node_indext &to,
    const dynamic_cfg_nodet &to_cfg_node);

  graphmlt::node_indext add_node(
    const dynamic_cfg_nodet &cfg_node);
};

#endif // CPROVER_2LS_SUMMARIZER_GRAPHML_WITNESS_EXT_H
