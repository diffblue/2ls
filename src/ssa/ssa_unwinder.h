/*******************************************************************\

Module: SSA Unwinder

Author: Peter Schrammel

\*******************************************************************/

#ifndef CPROVER_DELTACHECK_SSA_UNWINDER_H
#define CPROVER_DELTACHECK_SSA_UNWINDER_H

#include <util/message.h>

#include "../ssa/local_ssa.h"

class ssa_unwindert : public messaget
{
 public:
  ssa_unwindert() {}

  void unwind(local_SSAt &SSA, unsigned unwind);


 protected:
  //apply changes, must be called after replace and havoc
  void commit_nodes(local_SSAt::nodest &nodes);
  void commit_node(local_SSAt::nodet &node);
  local_SSAt::nodest new_nodes;
  std::set<local_SSAt::nodet::equalitiest::iterator> rm_equs;

  void rename(exprt &expr, unsigned index);
  void rename(local_SSAt::nodet &node, unsigned index);

 private:
  void merge_into_nodes(local_SSAt::nodest &nodes, 
			const local_SSAt::locationt &loc, 
                        const local_SSAt::nodet &new_n);

};

#endif
