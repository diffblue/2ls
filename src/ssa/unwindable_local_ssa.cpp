/*******************************************************************\

Module: SSA Unwinder Infrastructure

Author: Peter Schrammel, Saurabh Joshi

\*******************************************************************/

#include <iostream>

#include <util/find_symbols.h>
#include <util/rename_symbol.h>
#include <langapi/language_util.h>

#include "unwindable_local_ssa.h"

/*******************************************************************\

Function: unwindable_local_SSAt::increment_unwindings

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void unwindable_local_SSAt::increment_unwindings(int mode)
{
  if(mode==0) 
  {
    assert(current_unwindings.size()>=1);
    unsigned index = current_unwindings.size()-1;
    assert(current_unwindings[index]>=1);
    current_unwindings[index]++;
  }
  else if(mode>=1)
  {
    assert(mode==1);
    current_unwindings.push_back(0);
  }
  else //mode <=-1
  {
    for(int i=0;i>mode;i--)
      current_unwindings.pop_back();
  }
}

/*******************************************************************\

Function: unwindable_local_SSAt::decrement_unwindings

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void unwindable_local_SSAt::decrement_unwindings(int mode)
{
  if(mode==0) 
  {
    assert(current_unwindings.size()>=1);
    unsigned index = current_unwindings.size()-1;
    assert(current_unwindings[index]>=1);
    current_unwindings[index]--;
  }
  else if(mode>=1)
  {
    assert(mode==1);
    current_unwindings.push_back(current_unwinding);
  }
  else //mode <=-1
  {
    for(int i=0;i>mode;i--)
      current_unwindings.pop_back();
  }
}

/*******************************************************************\

Function: unwindable_local_SSAt::odometer_to_string

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string unwindable_local_SSAt::odometer_to_string(
  const odometert &odometer, unsigned level) const
{
  if(level<odometer.size())
    return "";
  if(level>odometer.size())
    level = odometer.size();
  std::string suffix = "";
  for(unsigned i=0;i<level;i++)
    suffix += "%" + std::to_string(odometer[i]);
  return suffix;
}

/*******************************************************************\

Function: unwindable_local_SSAt::rename

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

/*
void unwindable_local_SSAt::rename(symbol_exprt &expr, 
				  const odometert &unwindings)

{   
  std::string suffix = odometer_to_string(unwindings,
					  unwindings.size());
  expr.set_identifier(id2string(expr.get_identifier())+suffix);
}
*/

/*******************************************************************\

Function: unwindable_local_SSAt::name

  Inputs:

 Outputs:

 Purpose: overrides local_SSAt::name to add unwinder suffixes

\*******************************************************************/

symbol_exprt unwindable_local_SSAt::name(const ssa_objectt &object, 
					kindt kind, locationt def_loc) const
{
  symbol_exprt s = local_SSAt::name(object,kind,def_loc);
  loop_hierarchy_levelt::const_iterator lhl_it =
    loop_hierarchy_level.find(def_loc);
  unsigned def_level = 0;
  if(lhl_it != loop_hierarchy_level.end())
    def_level = lhl_it->second;
  std::string suffix = odometer_to_string(current_unwindings,
					  def_level);
  s.set_identifier(id2string(s.get_identifier())+suffix);
#if 1
  std::cout << "DEF_LOC: " << def_loc->location_number << std::endl;
  std::cout << "DEF_LEVEL: " << def_level << std::endl;
  std::cout << "RENAME_SYMBOL: "
	    << object.get_identifier() << " --> " 
	    << s.get_identifier() << std::endl;
#endif

  return s;
}

/*******************************************************************\

Function: unwindable_local_SSAt::read_rhs

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

/*
void unwindable_local_SSAt::read_rhs(exprt &expr, 
				  const odometert &unwindings,
				  local_SSAt::locationt loc)

{
  std::set<symbol_exprt> symbols;
  find_symbols(expr,symbols);
  if(symbols.empty())
    return;

  rename_symbolt rename_symbol;
  for(std::set<symbol_exprt>::const_iterator 
	it = symbols.begin();
      it != symbols.end(); ++it)
  {
    local_SSAt::locationt def_loc = 
      get_def_loc(to_symbol_expr(*it),loc);
    unsigned def_level = 
      loop_hierarchy_level[def_loc];
    std::string suffix = odometer_to_string(unwindings,def_level);
    symbol_exprt s = to_symbol_expr(local_SSAt::read_rhs(*it,loc));
    rename_symbol.insert_expr(it->get_identifier(),
			      id2string(s.get_identifier())+suffix);
#if 1
    std::cout << "DEF_LOC: " << def_loc->location_number << std::endl;
    std::cout << "DEF_LEVEL: " << def_level << std::endl;
    std::cout << "RENAME_SYMBOL: "
	      << it->get_identifier() << " --> " 
	      << id2string(s.get_identifier())+suffix << std::endl;
#endif
  }
  rename_symbol(expr);
#if 1
  std::cout << "UNWINDINGS_RENAME: " 
	    << from_expr(ns, "", expr) << std::endl;
#endif
}
*/

/*******************************************************************\

Function: unwindable_local_SSAt::compute_loop_hierarchy

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void unwindable_local_SSAt::compute_loop_hierarchy()
{
  unsigned level = 0;
  loop_hierarchy_level.clear();
  goto_programt::const_targett loophead = 
    goto_function.body.instructions.begin();
  forall_goto_program_instructions(i_it, goto_function.body)
  {
    bool found = false;
    for(std::set<goto_programt::targett>::const_iterator 
	  t_it = i_it->incoming_edges.begin();
	t_it != i_it->incoming_edges.end(); ++t_it)
    {
      if((*t_it)->location_number > i_it->location_number)
      {
	assert(!found); //target of two backwards edges
	loophead = i_it;
	level++;
	found = true;
      }
    }
    loop_hierarchy_level[i_it] = level;
    if(i_it->is_backwards_goto())
    {
      assert(loophead == i_it->get_target()); //backwards to current loop head
      assert(level>=1);
      level--;
    }
  }
}
