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

  concrete_transformerst(const namespacet& ns, const local_SSAt::nodest&);
  
  
  typedef std::set<symbol_exprt> symbols_sett;
  
  // information about symbols

    
  // output to stream
  void output(std::ostream &out);  

  // symbols
  symbols_sett symbols, free_symbols, bound_symbols;
   
protected:
  const namespacet &ns;

  void compute_symbols();

  exprt resolve_lb(const exprt &src, const local_SSAt& ssa);
  
  bool is_guard_cond(const exprt &) const;
};



#endif
