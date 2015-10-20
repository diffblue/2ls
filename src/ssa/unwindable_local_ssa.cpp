/*******************************************************************\

Module: SSA Unwinder Infrastructure

Author: Peter Schrammel, Saurabh Joshi

\*******************************************************************/

#include <iostream>

#include <util/find_symbols.h>
#include <util/rename_symbol.h>
#include <util/string2int.h>
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
  if(current_unwinding<0) //not yet unwind=0
    return "";
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
#if 0
  std::cout << "DEF_LOC: " << def_loc->location_number << std::endl;
  std::cout << "DEF_LEVEL: " << def_level << std::endl;
  std::cout << "RENAME_SYMBOL: "
	    << object.get_identifier() << " --> " 
	    << s.get_identifier() << std::endl;
#endif

  return s;
}

/*******************************************************************\

Function: unwindable_local_SSAt::rename

  Inputs:

 Outputs:

 Purpose: add unwinder suffixes

\*******************************************************************/

void unwindable_local_SSAt::rename(exprt &expr)
{
  if(expr.id()==ID_symbol)
  {
    symbol_exprt &s = to_symbol_expr(expr);
    locationt def_loc;
    //we could reuse name(), but then we would have to search in the ssa_objects
    //ENHANCEMENT: maybe better to attach base name, ssa name,
    //      and def_loc to the symbol_expr itself
    irep_idt id = get_ssa_name(s,def_loc);
    loop_hierarchy_levelt::const_iterator lhl_it =
      loop_hierarchy_level.find(def_loc);
    unsigned def_level = 0;
    if(lhl_it != loop_hierarchy_level.end())
      def_level = lhl_it->second;
    std::string suffix = odometer_to_string(current_unwindings,
					    def_level);
    s.set_identifier(id2string(id)+suffix);
  }
  Forall_operands(it,expr)
    rename(*it);
}

/*******************************************************************\

Function: unwindable_local_SSAt::get_ssa_name

  Inputs:

 Outputs:

 Purpose: retrieve ssa name, 

\*******************************************************************/

irep_idt unwindable_local_SSAt::get_ssa_name(
  const symbol_exprt &symbol_expr, locationt &loc)
{
  std::string s =  id2string(symbol_expr.get_identifier()); 
  std::size_t pos2 = s.find("%");
  std::size_t pos1 = s.find_last_of("#");
  if(pos1==std::string::npos)
    return irep_idt(s);
  if(pos2==std::string::npos)
    pos2 = s.size();
  loc = find_location_by_number(safe_string2unsigned(s.substr(pos1,pos2)));
  return irep_idt(s.substr(pos2));
}


/*******************************************************************\

Function: unwindable_local_SSAt::compute_loop_hierarchy

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void unwindable_local_SSAt::compute_loop_hierarchy()
{
  loop_hierarchy_level.clear();
  std::list<goto_programt::const_targett> loopheads;
  forall_goto_program_instructions(i_it, goto_function.body)
  {
    bool found = false;
    for(std::set<goto_programt::targett>::const_iterator 
	  t_it = i_it->incoming_edges.begin();
	t_it != i_it->incoming_edges.end(); ++t_it)
    {
      if((*t_it)->is_backwards_goto())
      {
	assert(!found); //target of two backwards edges
	loopheads.push_back(i_it);
	found = true;
      }
    }
    loop_hierarchy_level[i_it] = loopheads.size();
    if(i_it->is_backwards_goto())
    {
      assert(!loopheads.empty());
      assert(loopheads.back() == i_it->get_target()); //backwards to current loop head
      loopheads.pop_back();
    }
  }
}
