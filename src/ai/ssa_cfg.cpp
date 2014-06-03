#include <fstream>

#include <util/find_symbols.h>

#include "ssa_cfg.h"


ssa_cfgt::ssa_cfgt(const local_SSAt &local_ssa) :
  goto_function(local_ssa.goto_function)
{

  // NOTE: we assume that the entry node has the smallest number
  entry_node=local_ssa.goto_function.body.instructions.front().location_number;

  // map from expression to location that writes it
  
  typedef std::map<unsigned, local_SSAt::locationt> location_mapt;
  location_mapt location_map;
  
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
    local_SSAt::locationt loc=node_it->first;

    unsigned node=loc->location_number;
    location_map[node]=loc;
    
    nodes.insert(node);    
        
    const local_SSAt::nodet &ssa_node=node_it->second;
    
    
    std::cout << "Node " << node << std::endl;
         
    std::cout << "incoming: " ;
    /*
    
    for(local_SSAt::nodet::incomingt::iterator
        incoming_it=ssa_node.incoming.begin();
        incoming_it!=ssa_node.incoming.end();
        ++incoming_it)
    {
      std::cout << (*incoming_it)->location_number << " ";
    
    }
    
    */
    
    const guard_mapt::entryt& entry=local_ssa.guard_map[loc];
    
    for(guard_mapt::incomingt::const_iterator
        incoming_it=entry.incoming.begin();
        incoming_it!=entry.incoming.end();
        ++incoming_it)
    {
      std::cout << incoming_it->guard_source->location_number << " ";
    }
    
    std::cout << std::endl;
         
         
    for(local_SSAt::nodet::equalitiest::const_iterator
        e_it=ssa_node.equalities.begin();
        e_it!=ssa_node.equalities.end();
        e_it++)
    {   
      find_symbols(e_it->op1(), reader[node]);

      writer[e_it->op0()]=node;

      std::cout << from_expr(*e_it) << std::endl;

    }

    for(local_SSAt::nodet::constraintst::const_iterator
        c_it=ssa_node.constraints.begin();
        c_it!=ssa_node.constraints.end();
        c_it++)
    {
      find_symbols(c_it->op0(), reader[node]);
      find_symbols(c_it->op1(), reader[node]);
    }
  }
  

  typedef std::pair<unsigned, unsigned> dept;
  
  
  
  typedef std::set<std::pair<unsigned, unsigned> > depst;
  depst deps;
    
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


  unsigned connections=0;
  
  for(depst::iterator
      dep_it=deps.begin();
      dep_it!=deps.end();
      ++dep_it)
  {
    ssa_cfg_edget edge;
    edge.pred=dep_it->first;
    edge.succ=dep_it->second;
    
    local_SSAt::locationt loc=location_map[edge.succ];
    
    local_SSAt::nodest::const_iterator node_iterator=local_ssa.nodes.find(loc);
    if(node_iterator!=local_ssa.nodes.end())
    {    
      const local_SSAt::nodet &ssa_node=node_iterator->second;
      edge.transformer.equalities=ssa_node.equalities;
      edge.transformer.constraints=ssa_node.constraints;
    }
    
    adjacency[edge.pred].insert(edge);
    
    ++connections;
  }
  
  std::cout << "# of connections " << connections << " #adjacency " << adjacency.size() <<" #reader " << reader.size() << " #writer " << writer.size() << std::endl;
  
  // determine function name
  
  
  dot_output(std::cout);
}

void ssa_cfgt::dot_output(std::ostream &out)
{

  out << "digraph art {" << std::endl;


  for(nodest::iterator 
      node_it=nodes.begin();
      node_it!=nodes.end();
      ++node_it)
  {
    unsigned node=*node_it;
    out << node << "[label=\""<<node<<"\"];\n";
  }


  for(adjacencyt::iterator 
      entry_it=adjacency.begin();
      entry_it!=adjacency.end();
      ++entry_it)
  {

    edgest &edges=entry_it->second;

    for(edgest::iterator
        edge_it=edges.begin();
        edge_it!=edges.end();
        ++edge_it)
     {
        const ssa_cfg_edget &edge=*edge_it;

        out << edge.pred << " -> " << edge.succ;

        out << " [label=\"";

        const ssa_cfg_concrete_transformert &transformer=edge.transformer;

        for(ssa_cfg_concrete_transformert::equalitiest::const_iterator
            e_it=transformer.equalities.begin();
            e_it!=transformer.equalities.end();
            e_it++)
        {   
          out << (e_it!=transformer.equalities.begin() ? " && " : "") << from_expr(*e_it);
        }

        for(ssa_cfg_concrete_transformert::constraintst::const_iterator
            c_it=transformer.constraints.begin();
            c_it!=transformer.constraints.end();
            c_it++)
        {    
          out << (c_it!=transformer.constraints.begin() ? " && " : "") << from_expr(*c_it);
        }

        out << "\"];\n";
    }
  }
  
  out << "}"<<std::endl;
}


