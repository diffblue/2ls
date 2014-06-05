#include <algorithm>
#include <util/simplify_expr.h>
#include <util/prefix.h>
#include <util/replace_expr.h>
#include <util/find_symbols.h>
#include <util/string2int.h>

#include "concrete_transformers.h"




bool concrete_transformerst::is_guard_cond(const exprt &expr) const
{
  if(expr.id()==ID_symbol)
  {
    const symbol_exprt &symbol=to_symbol_expr(expr);
  
    if(   has_prefix(id2string(symbol.get_identifier()), "ssa::$guard")
       || has_prefix(id2string(symbol.get_identifier()), "ssa::$cond"))
    {  
      return true;
    }
  }
   
  return false;
}


concrete_transformerst::concrete_transformerst(const namespacet &_ns, const local_SSAt::nodest &nodes)
: ns(_ns)
{
  replace_mapt replace_map;

  // collect the guards
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
      if(is_guard_cond(e.op0())) 
      {
        std::cout << "symbol " << from_expr(e.op0()) << " := " << from_expr(e.op1()) << std::endl;
      
        exprt tmp=e.op1();

        replace_map[e.op0()]=tmp;
      }
    }
  }  

  bool change=true;
  
  while(change)
  {
    change=false;
    
    for(replace_mapt::iterator 
        it=replace_map.begin();
        it!=replace_map.end();
        ++it)
    {
      exprt tmp=it->second;
      replace_expr(replace_map, tmp);
      simplify(tmp, ns);
      
      change=tmp!=it->second || change;
      tmp.swap(it->second);
    }
  }

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
    
      if(is_guard_cond(e.op0()))
        continue; // skip
      else {
        exprt tmp(e.op1());
        replace_expr(replace_map, tmp);
      
        transformers.push_back(concrete_transformert(e.op0(), tmp));
      }
      
    }
    

    // add all constraints
    for(unsigned i=0; i<node.constraints.size(); ++i)
    {
      const exprt &e=node.constraints[i];
      exprt tmp(e);
      replace_expr(replace_map, tmp);
      transformers.push_back(concrete_transformert(tmp));
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


