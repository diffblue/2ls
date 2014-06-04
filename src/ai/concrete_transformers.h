#ifndef CPROVER_CONCRETE_TRANSFORMERS_H
#define CPROVER_CONCRETE_TRANSFORMERS_H

#include <goto-programs/goto_functions.h>

#include "fixpoint.h"
#include "concrete_transformer.h"

#include "../ssa/local_ssa.h"

class concrete_transformerst
{
public:

  typedef std::vector<concrete_transformert> transformer_cont;
  transformer_cont transformers;
  
  typedef goto_functionst::goto_functiont goto_functiont;

  void convert(const local_SSAt &local_ssa);
  
  void output(std::ostream &out);
    
  // joins at loop heads
};



#endif
