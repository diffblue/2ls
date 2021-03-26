/*******************************************************************\

Module: SSA CFA extension for GraphML output

Author: Peter Schrammel

\*******************************************************************/

/// \file
/// SSA CFA extension for GraphML output

#include "graphml_witness_ext.h"

/// proof witness TODO: works only for inlined programs
void graphml_witness_extt::operator()(
  const summary_checker_baset &summary_checker)
{
  irep_idt function_name=goto_functionst::entry_point();
  const unwindable_local_SSAt &ssa=
    static_cast<const unwindable_local_SSAt &>(
      summary_checker.ssa_db.get(function_name));
  const ssa_local_unwindert &ssa_unwinder=
  summary_checker.ssa_unwinder.get(function_name);

  graphml.key_values["sourcecodelang"]="C";

  dynamic_cfgt cfg;
  if(summary_checker.summary_db.exists(function_name))
  {
    const summaryt &summary=summary_checker.summary_db.get(function_name);
    cfg(ssa_unwinder, ssa, summary);
  }
  else
  {
    cfg(ssa_unwinder, ssa, summaryt());
  }


  // CFG to CFA
  const graphmlt::node_indext sink=graphml.add_node();
  graphml[sink].node_name="sink";
  graphml[sink].is_violation=false;
  graphml[sink].has_invariant=false;

  std::vector<graphmlt::node_indext> index_map;
  index_map.resize(cfg.size());
  for(std::size_t i=0; i<cfg.size(); ++i)
  {
    const source_locationt &source_location=cfg[i].id.pc->source_location;

    if(source_location.is_nil() ||
       source_location.get_file().empty() ||
       source_location.get_file()=="<built-in-additions>" ||
       source_location.get_line().empty())
    {
      index_map[i]=sink;
      continue;
    }

    const graphmlt::node_indext node=add_node(cfg[i]);
    index_map[i]=node;
  }
  for(std::size_t i=0; i<cfg.size(); ++i)
  {
    for(const auto &e : cfg[i].out)
    {
      if(index_map[i]!=sink && index_map[e.first]!=sink)
        add_edge(index_map[i], cfg[i], index_map[e.first], cfg[e.first]);
    }
  }
}

graphmlt::node_indext graphml_witness_extt::add_node(
  const dynamic_cfg_nodet &cfg_node)
{
  const graphmlt::node_indext node=graphml.add_node();
  graphml[node].node_name=cfg_node.id.to_string();
  graphml[node].has_invariant=cfg_node.assumption.is_not_nil();
  if(cfg_node.assumption.is_not_nil())
  {
    std::ostringstream invs;
    invs << from_expr(ns, "", cfg_node.assumption);
    graphml[node].invariant=invs.str();
    graphml[node].invariant_scope=id2string(cfg_node.id.pc->function);
  }
  return node;
}

void graphml_witness_extt::add_edge(
  const graphmlt::node_indext &from,
  const dynamic_cfg_nodet &from_cfg_node,
  const graphmlt::node_indext &to,
  const dynamic_cfg_nodet &to_cfg_node)
{
  const source_locationt &source_location=from_cfg_node.id.pc->source_location;

  xmlt edge("edge");
  edge.set_attribute("source", graphml[from].node_name);
  edge.set_attribute("target", graphml[to].node_name);

  {
    xmlt &data_f=edge.new_element("data");
    data_f.set_attribute("key", "originfile");
    data_f.data=id2string(source_location.get_file());

    xmlt &data_l=edge.new_element("data");
    data_l.set_attribute("key", "startline");
    data_l.data=id2string(source_location.get_line());

    if(to_cfg_node.is_loop_head)
    {
      xmlt &data_l=edge.new_element("data");
      data_l.set_attribute("key", "enterLoopHead");
      data_l.data="true";
    }
  }

  graphml[to].in[from].xml_node=edge;
  graphml[from].out[to].xml_node=edge;
}
