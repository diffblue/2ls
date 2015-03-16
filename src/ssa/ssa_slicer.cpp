#include <iostream>

#include <util/find_symbols.h>
#include <util/string2int.h>

#include "local_ssa.cpp"

void print_symbols(std::string msg, const find_symbols_sett &symbols)
{
  std::cout << msg << ": " << std::endl;
  for(find_symbols_sett::const_iterator
	s_it=symbols.begin();  s_it!=symbols.end(); s_it++)
    std::cout << "  " << *s_it << std::endl;

}

void ssa_slicert::operator()(std::list<exprt> &dest,
			     const local_SSAt &src) 
{
  //collect symbols in assertions
  find_symbols_sett new_symbols;
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
      find_symbols(*a_it,new_symbols);
    }
  }
#ifdef DEBUG
  print_symbols("symbols in assertions",new_symbols);
#endif
  if(new_symbols.empty()) return;

  //build map symbol -> (definition, constraint set)
  symbol_mapt symbol_map;
  sliced_equalities = 0;
  sliced_constraints = 0;
  
  for(local_SSAt::nodest::const_iterator n_it = src.nodes.begin();
      n_it != src.nodes.end(); n_it++)
  {
    for(local_SSAt::nodet::equalitiest::const_iterator
	  e_it=n_it->equalities.begin();
        e_it!=n_it->equalities.end();
        e_it++)
    {
      find_symbols_sett e_symbols;
      find_symbols(e_it->lhs(),e_symbols);

      for(find_symbols_sett::const_iterator
	    s_it=e_symbols.begin();  s_it!=e_symbols.end(); s_it++)
      {
	symbol_map[*s_it];
	symbol_map[*s_it].def = e_it;
	symbol_map[*s_it].def_node = n_it;
      }
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
	if(symbol_map.find(*s_it)==symbol_map.end()) continue;
	symbol_map[*s_it].constraints.push_back(constr_infot());
	constr_infot &constr_info = symbol_map[*s_it].constraints.back();
	constr_info.constr = c_it;
	constr_info.node = n_it;
      }
    }
    //statistics
    if(!n_it->marked)
    {
      sliced_equalities += n_it->equalities.size();
      sliced_constraints += n_it->constraints.size();
    }
  }
    //statistics
  std::cout << "Total equalities: " << sliced_equalities
	    << ", total constraints: " << sliced_constraints << std::endl;

  //compute backwards dependencies and add to formula on-the-fly
  find_symbols_sett symbols_seen; 
  while(!new_symbols.empty())
  {
    find_symbols_sett old_symbols = new_symbols;
    
#ifdef DEBUG
    print_symbols("new symbols",new_symbols);
#endif
    
    new_symbols.clear();
    for(find_symbols_sett::const_iterator
	  s_it=old_symbols.begin();  s_it!=old_symbols.end(); s_it++)
    {
      irep_idt sym = *s_it;
      if(symbols_seen.find(sym)!=symbols_seen.end()) continue;
      if(symbol_map.find(sym)==symbol_map.end())
      {
	//handle loopback variables
	//here it's getting a bit ugly
	std::string sym_str = id2string(sym);
	size_t pos1 = sym_str.find("#lb");
	if(pos1==std::string::npos) continue;
	size_t pos2 = sym_str.find("%",pos1);
	irep_idt basename = sym_str.substr(0,pos1);
	std::string unwinder_suffix = "";
	if(pos2<sym_str.size()) unwinder_suffix = sym_str.substr(pos2);
	unsigned location_number =
	  safe_string2unsigned(sym_str.substr(pos1+3,pos2));
	local_SSAt::locationt location =
	  src.find_location_by_number(location_number);

#ifdef DEBUG
	std::cout << "basename = " << basename
		  << ", location_number = " << location_number
		  << ", unwinder_suffix = " << unwinder_suffix
		  << std::endl;
#endif
	const symbolt &symbol = src.ns.lookup(basename);
	sym = id2string(to_symbol_expr(src.
		read_lhs(symbol.symbol_expr(),location)).
			get_identifier())+unwinder_suffix;
	irep_idt new_guard_symbol =
	  id2string(src.guard_symbol(location).get_identifier())+unwinder_suffix;
	new_symbols.insert(new_guard_symbol);
#ifdef DEBUG
	std::cout << "new symbol = " << sym << std::endl;
#endif
      }
      assert(symbol_map.find(sym)!=symbol_map.end());
      const symbol_infot &symbol_info = symbol_map[sym];
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
	//statistics
	sliced_equalities--;
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
	  //statistics
	  sliced_constraints--;
	}
      }
    }
    symbols_seen.insert(old_symbols.begin(),old_symbols.end());
  }
  //statistics
  std::cout << "Sliced equalities: " << sliced_equalities
	    << ", sliced constraints: " << sliced_constraints << std::endl;
}
