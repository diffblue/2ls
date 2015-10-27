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
    assert(current_unwindings[index]<std::numeric_limits<unsigned>::max());
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
//TODO: remove this
/*  if(level<odometer.size())
    return "";*/
  if(level>odometer.size())
    level = odometer.size();
  std::string unwind_suffix = "";
  for(unsigned i=0;i<level;i++)
    unwind_suffix += "%" + std::to_string(odometer[i]);
  return unwind_suffix;
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
  std::string unwind_suffix = odometer_to_string(current_unwindings,
					  def_level);
  s.set_identifier(id2string(s.get_identifier())+unwind_suffix+suffix);
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

Function: unwindable_local_SSAt::nondet_symbol

  Inputs:

 Outputs:

 Purpose: overrides local_SSAt::nondet_symbol to add unwinder suffixes

\*******************************************************************/

exprt unwindable_local_SSAt::nondet_symbol(std::string prefix, 
  const typet &type, locationt loc, unsigned counter) const
{
  std::string unwind_suffix = odometer_to_string(current_unwindings,
					  current_unwindings.size());
  exprt s(ID_nondet_symbol, type);
  const irep_idt identifier=
    prefix+
    i2string(loc->location_number)+
    "."+i2string(counter)+unwind_suffix+suffix;
  s.set(ID_identifier, identifier);
#if 0
  std::cout << "DEF_LOC: " << loc->location_number << std::endl;
  std::cout << "DEF_LEVEL: " << current_unwindings.size() << std::endl;
  std::cout << "RENAME_SYMBOL: "
	    << s.get(ID_identifier) << std::endl;
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
    std::string unwind_suffix = odometer_to_string(current_unwindings,
					    def_level);
    s.set_identifier(id2string(id)+unwind_suffix);
#if 0
  std::cout << "DEF_LOC: " << def_loc->location_number << std::endl;
  std::cout << "DEF_LEVEL: " << def_level << std::endl;
  std::cout << "O.size: " << current_unwindings.size() << std::endl;
  std::cout << "current: " << current_unwinding << std::endl;
  std::cout << "RENAME_SYMBOL: "
	    << id << " --> " 
	    << s.get_identifier() << std::endl;
#endif
  }
  if(expr.id()==ID_nondet_symbol)
  {
    std::string unwind_suffix = odometer_to_string(current_unwindings,
						   current_unwindings.size());
    expr.set(ID_identifier, 
	     id2string(expr.get(ID_identifier))+unwind_suffix+suffix);
  }
  Forall_operands(it,expr)
    rename(*it);
}

/*******************************************************************\

Function: unwindable_local_SSAt::get_ssa_name

  Inputs:

 Outputs:

 Purpose: retrieve ssa name and location

\*******************************************************************/

irep_idt unwindable_local_SSAt::get_ssa_name(
  const symbol_exprt &symbol_expr, locationt &loc)
{
  std::string s =  id2string(symbol_expr.get_identifier()); 
#if 0
  std::cout << "id: " << s << std::endl;
#endif
  std::size_t pos2 = s.find("%");
  std::size_t pos1 = s.find_last_of("#");
  if(pos1==std::string::npos)
    return irep_idt(s);
  if(pos2==std::string::npos)
    pos2 = s.size();
  if(s.substr(pos1+1,2) == "lb") pos1 += 2;
  else if(s.substr(pos1+1,2) == "ls") pos1 += 2;
  else if(s.substr(pos1+1,3) == "phi") pos1 += 3;
  else if((pos2 == pos1+13) && (s.substr(pos1+1,12) == "return_value")) 
    return irep_idt(s);
#if 0
  std::cout << s << ", " << s.substr(pos1+1,pos2-pos1-1) << ", " << s.substr(0,pos2) << std::endl;
#endif
  loc = find_location_by_number(
    safe_string2unsigned(s.substr(pos1+1,pos2-pos1-1)));
  return irep_idt(s.substr(0,pos2));
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

#if 0
    std::cout << "location: " << i_it->location_number << std::endl;
    std::cout << "- targets:";
    for(goto_programt::targetst::const_iterator 
	  t_it = i_it->targets.begin();
	t_it != i_it->targets.end(); ++t_it)
      std::cout << " " << i_it->get_target()->location_number;
    std::cout << std::endl;
#endif

    for(std::set<goto_programt::targett>::const_iterator 
	  t_it = i_it->incoming_edges.begin();
	t_it != i_it->incoming_edges.end(); ++t_it)
    {

#if 0
      std::cout << "- incoming: " << (*t_it)->location_number << std::endl;
#endif

      //cannot use ->is_backwards_goto() here
      if((*t_it)->location_number>=i_it->location_number)
      {
	assert(!found); //should not be target of two backwards edges
	found = true;

#if 0
	std::cout << "- new: " << i_it->location_number << std::endl;
#endif

	loopheads.push_back(i_it);
      }
    }
    loop_hierarchy_level[i_it] = loopheads.size();
    if(i_it->is_backwards_goto())
    {

#if 0
	std::cout << "- current: " << 
	  loopheads.back()->location_number << 
	  ", backwards: " << 
	  i_it->get_target()->location_number << std::endl;
#endif

      assert(!loopheads.empty());
      //must be backwards goto to current loop head
      assert(loopheads.back() == i_it->get_target()); 
      loopheads.pop_back();
    }
  }
}
