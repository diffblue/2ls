/*******************************************************************\

Module: SSA Unwinder Infrastructure

Author: Peter Schrammel, Saurabh Joshi

\*******************************************************************/

#include <iostream>

#include <limits>

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
		kindt kind, locationt def_loc, locationt current_loc) const
{
  symbol_exprt s = local_SSAt::name(object,kind,def_loc);
  unsigned def_level = get_def_level(def_loc, current_loc);
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

Function: unwindable_local_SSAt::get_def_level

  Inputs:

 Outputs:

 Purpose: returns the definition level of a variable in the loop 
          hierarchy

\*******************************************************************/

unsigned unwindable_local_SSAt::get_def_level(
  locationt def_loc, locationt current_loc) const
{
  loop_hierarchy_levelt::const_iterator lhl_it =
    loop_hierarchy_level.find(def_loc);
  unsigned def_level = 0;
  if(lhl_it != loop_hierarchy_level.end())
  {
    def_level = lhl_it->second.level;
    // If a variable is defined in an other loop (that is on 
    //   the same level as we are [we should should check that]
    // then we have to take the "merged version" 
    // The reason for this is that the "exit mergers" actually
    // introduce a new SSA variable version on the context level of a loop.
    loop_hierarchy_levelt::const_iterator current_lhl =
      loop_hierarchy_level.find(current_loc);
#if 0
  std::cout << "def_level: " << def_level << std::endl;
  std::cout << "loop_number: " << lhl_it->second.loop_number << std::endl;
  std::cout << "current_location: " << current_loc->location_number << std::endl;
  std::cout << "current_loop_number: " << current_lhl->second.loop_number << std::endl;
#endif
    if(current_lhl != loop_hierarchy_level.end() &&
       lhl_it->second.loop_number != current_lhl->second.loop_number &&
       lhl_it->second.level == current_lhl->second.level)
    {
      if(current_lhl->second.level>0)
        def_level = current_lhl->second.level-1;
      else 
	def_level = 0;
    }
  }
  return def_level;
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

void unwindable_local_SSAt::rename(exprt &expr, locationt current_loc)
{
  if(expr.id()==ID_symbol)
  {
    symbol_exprt &s = to_symbol_expr(expr);
    locationt def_loc;
    //we could reuse name(), but then we would have to search in the ssa_objects
    //ENHANCEMENT: maybe better to attach base name, ssa name,
    //      and def_loc to the symbol_expr itself
    irep_idt id = get_ssa_name(s,def_loc);
    unsigned def_level = get_def_level(def_loc, current_loc);
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
    rename(*it, current_loc);
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
  loc = get_location(
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
  goto_programt::const_targett i_it = goto_function.body.instructions.end();
  do
  {
    --i_it;

#if 0
    std::cout << "location: " << i_it->location_number << std::endl;
    if(i_it->is_goto())
      std::cout << "- target: " << i_it->get_target()->location_number
		<< std::endl;
#endif

    if(i_it->is_backwards_goto())
    {
      loopheads.push_back(i_it->get_target());
      loop_hierarchy_level[loopheads.back()].loop_number = i_it->loop_number;
    }

    if(!loopheads.empty())
    {
      loop_hierarchy_level[i_it].loop_number = 
	loop_hierarchy_level[loopheads.back()].loop_number;
      loop_hierarchy_level[i_it].level = loopheads.size();

#if 0
      std::cout << "- current: " << 
	loopheads.back()->location_number  << std::endl;
#endif
	
      if(i_it == loopheads.back())
      {
#if 0
	std::cout << "- is loop head" << std::endl;
#endif
	loopheads.pop_back();
      }
    }
  }
  while(i_it != goto_function.body.instructions.begin());
}
