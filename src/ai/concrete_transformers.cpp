#include <algorithm>

#include <util/find_symbols.h>
#include <util/string2int.h>

#include "concrete_transformers.h"


concrete_transformerst::concrete_transformerst(const local_SSAt::nodest &nodes)
{

  for(local_SSAt::nodest::const_iterator 
      node_it=nodes.begin();
      node_it!=nodes.end();
      ++node_it)
  {
    const local_SSAt::nodet &node=node_it->second;

    // add all equalities
    for(unsigned i=0; i<node.equalities.size(); ++i)
    {
      const equal_exprt &e=node.equalities[i];
      transformers.push_back(concrete_transformert(e.op0(), e.op1()));
    }

    // add all constraints
    for(unsigned i=0; i<node.constraints.size(); ++i)
    {
      const exprt &e=node.constraints[i];
      transformers.push_back(concrete_transformert(e));
    }
  }
  
  compute_symbols();
}

void concrete_transformerst::compute_symbols()
{

  // all symbols
  for(unsigned i=0; i<transformers.size(); ++i)
  {
    if(transformers[i].is_equality())
    {  
      find_symbols(transformers[i].op0, symbols);
      find_symbols(transformers[i].op1, symbols);
      find_symbols(transformers[i].op0, bound_symbols);     
    } else
    {
      find_symbols(transformers[i].op1, symbols);    
    }
  }

  // free symbols
  std::set_difference(symbols.begin(),
                      symbols.end(),
                      bound_symbols.begin(),
                      bound_symbols.end(),
                      std::inserter(free_symbols, free_symbols.end()));
}

void concrete_transformerst::output(std::ostream &out)
{
}


