#include <util/find_symbols.h>

#include "ssa_cfg.h"


ssa_cfgt::ssa_cfgt(const local_SSAt &local_ssa) {
  // map from expression to location that writes it
  typedef std::map<exprt, unsigned> writert;
  writert writer;
  
  // map from expression to locations that read it
  typedef std::map<unsigned, std::set<exprt> > readert;
  readert reader;

  for(local_SSAt::nodest::const_iterator 
      node_it=local_ssa.nodes.begin();
      node_it!=local_ssa.nodes.end();
      ++node_it)
  {
    const local_SSAt::locationt &loc=node_it->first;

    unsigned node=loc->location_number;
    
    nodes.insert(node);    
        
    const local_SSAt::nodet &ssa_node=node_it->second;
     
    for(local_SSAt::nodet::equalitiest::const_iterator
        e_it=ssa_node.equalities.begin();
        e_it!=ssa_node.equalities.end();
        e_it++)
    {   
      find_symbols(e_it->op1(), reader[node]);

      writer[e_it->op0()]=node;
    }

    for(local_SSAt::nodet::constraintst::const_iterator
        c_it=ssa_node.constraints.begin();
        c_it!=ssa_node.constraints.end();
        c_it++)
    {
    
      std::set<exprt> dest;
      find_symbols(c_it->op0(), reader[node]);
      find_symbols(c_it->op1(), reader[node]);
    }
  }
  

  typedef std::pair<unsigned, unsigned> dept;
  typedef std::set<std::pair<unsigned, unsigned> > depst;
  depst deps;
  
  
  // control dependencies ?
  
  // def-use dependencies
  for(readert::iterator
      reader_it=reader.begin();
      reader_it!=reader.end();
      ++reader_it)
  {
    unsigned node=reader_it->first;
    const std::set<exprt> &reads=reader_it->second;
  
    for(std::set<exprt>::iterator
        expr_it=reads.begin();
        expr_it!=reads.end();
        ++expr_it)
    {
      if(writer.find(*expr_it)==writer.end())
        continue;
    
      unsigned def_node=writer[*expr_it];
      deps.insert(dept(def_node, node));
    }
  }
  
  for(depst::iterator
      dep_it=deps.begin();
      dep_it!=deps.end();
      ++dep_it)
  {
  }
}
