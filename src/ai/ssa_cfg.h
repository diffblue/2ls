#ifndef CPROVER_SSA_CFG_H
#define CPROVER_SSA_CFG_H

#include <goto-programs/goto_functions.h>

#include "fixpoint.h"
#include "../ssa/local_ssa.h"

struct ssa_cfg_concrete_transformert {
  typedef std::vector<equal_exprt> equalitiest;
  equalitiest equalities;

  typedef std::vector<exprt> constraintst;
  constraintst constraints;
};

struct ssa_cfg_edget {
  ssa_cfg_concrete_transformert transformer;
  unsigned pred, succ;
};


class ssa_cfgt : 
  public cfgt<unsigned, 
              ssa_cfg_edget, 
              ssa_cfg_concrete_transformert>
{
public:
  typedef goto_functionst::goto_functiont goto_functiont;

  ssa_cfgt(const local_SSAt &local_ssa);
  
  virtual edgest &get_succ_edges(unsigned n) {
    return adjacency[n];
  }
  
  virtual unsigned get_pred_node(ssa_cfg_edget &e) {
    return e.pred;
  }
  
  virtual unsigned get_succ_node(ssa_cfg_edget &e) {
    return e.succ;
  }
  
  virtual ssa_cfg_concrete_transformert &get_transformer(ssa_cfg_edget &e) {
    return e.transformer;
  }
  
  virtual nodest &get_nodes() {
    return nodes;
  }
  
  
  // Graphviz output
  void dot_output(std::ostream &out);
  
protected:
  
  const goto_functiont &goto_function;
  
  nodest nodes;
  
  typedef hash_map_cont<unsigned, edgest> adjacencyt;
  adjacencyt adjacency;
};



#endif
