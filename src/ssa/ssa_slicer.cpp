#include <util/find_symbols.h>

#include "local_ssa.cpp"

void ssa_slicert::operator()(std::list<exprt> &dest,
			     const local_SSAt &src) 
{
  //collect symbols in assertions
  find_symbols_sett symbols;
  for(local_SSAt::nodest::const_iterator n_it = src.nodes.begin();
    n_it != src.nodes.end(); n_it++)
  {
    if(n_it->marked) continue;
    if(n_it->assertions.empty()) continue;
    for(local_SSAt::nodet::assertionst::const_iterator
	  a_it=n_it->assertions.begin();
	a_it!=n_it->assertions.end();
	a_it++)
    {
      find_symbols(*a_it,symbols);
    }
  }
  if(symbols.empty()) return;

  //build map symbol -> (definition, constraint set)
  symbol_mapt symbol_map;

  for(local_SSAt::nodest::const_iterator n_it = src.nodes.begin();
      n_it != src.nodes.end(); n_it++)
  {
    for(local_SSAt::nodet::equalitiest::const_iterator
	  e_it=n_it->equalities.begin();
        e_it!=n_it->equalities.end();
        e_it++)
    {
      irep_idt id;
      if(e_it->lhs().id()==ID_symbol) 
      {
	id = to_symbol_expr(e_it->lhs()).get_identifier();
      }
      else assert(false);
      symbol_map[id];
      symbol_map[id].def = e_it;
      symbol_map[id].def_node = n_it;
    }
    for(local_SSAt::nodet::constraintst::const_iterator
	  c_it=n_it->constraints.begin();
        c_it!=n_it->constraints.end();
        c_it++)
    {
      find_symbols_sett c_symbols;
      find_symbols(*c_it,c_symbols);
      for(find_symbols_sett::const_iterator
	  s_it=c_symbols.begin();  s_it!=c_symbols.end(); s_it++)
      {
	symbol_map[*s_it].constraints.push_back(constr_infot());
	constr_infot &constr_info = symbol_map[*s_it].constraints.back();
	constr_info.constr = c_it;
	constr_info.node = n_it;
      }
    }
  }
  //compute backwards dependencies and add to formula on-the-fly
 find_symbols_sett new_symbols = symbols;
 while(!new_symbols.empty())
 {
   find_symbols_sett old_symbols = new_symbols;
   new_symbols.clear();
   for(find_symbols_sett::const_iterator
	 s_it=old_symbols.begin();  s_it!=old_symbols.end(); s_it++)
   {
     if(symbols.find(*s_it)!=symbols.end()) continue;
     const symbol_infot &symbol_info = symbol_map[*s_it];
     // add dependency
     find_symbols(symbol_info.def->rhs(),new_symbols);
     // add to solver
     if(!symbol_info.def_node->marked) 
     {
       if(!symbol_info.def_node->enabling_expr.is_true()) 
	 dest.push_back(implies_exprt(
	 symbol_info.def_node->enabling_expr,*(symbol_info.def)));
       else
	 dest.push_back(*(symbol_info.def));
     }
     for(constraint_sett::const_iterator
	   c_it=symbol_info.constraints.begin();
	 c_it!=symbol_info.constraints.end();
	 c_it++)
     {
       // add dependency
       find_symbols(*(c_it->constr),new_symbols);
       // add to solver
       if(!c_it->node->marked) 
       {
	 if(!c_it->node->enabling_expr.is_true()) 
	   dest.push_back(implies_exprt(
	      c_it->node->enabling_expr,*(c_it->constr)));
	 else
	   dest.push_back(*(c_it->constr));
       }
     }
   }
 }
}
