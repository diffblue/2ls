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
  void commit_nodes(local_SSAt::nodest &nodes,
                    local_SSAt::nodest::iterator n_pos);
  local_SSAt::nodest new_nodes;

  void rename(exprt &expr, unsigned index);
  void rename(local_SSAt::nodet &node, unsigned index);

};

#endif
