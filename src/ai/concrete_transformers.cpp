#include <fstream>

#include <util/find_symbols.h>

#include "concrete_transformers.h"


void concrete_transformerst::convert(const local_SSAt::nodest &nodes)
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
}

void concrete_transformerst::output(std::ostream &out)
{
}


