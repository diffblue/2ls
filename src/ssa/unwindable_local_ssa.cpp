/*******************************************************************\

Module: SSA Unwinder Infrastructure

Author: Peter Schrammel, Saurabh Joshi

\*******************************************************************/

/// \file
/// SSA Unwinder Infrastructure

#include <iostream>

#include <limits>

#include <util/find_symbols.h>
#include <util/rename_symbol.h>
#include <util/string2int.h>
#include <langapi/language_util.h>

#include "unwindable_local_ssa.h"

void unwindable_local_SSAt::increment_unwindings(int mode)
{
  if(mode==0)
  {
    assert(current_unwindings.size()>=1);
    unsigned index=current_unwindings.size()-1;
    assert(current_unwindings[index]<std::numeric_limits<unsigned>::max());
    current_unwindings[index]++;
  }
  else if(mode>=1)
  {
    assert(mode==1);
    current_unwindings.push_back(0);
  }
  else // mode <=-1
  {
    for(int i=0; i>mode; --i)
      current_unwindings.pop_back();
  }
}

void unwindable_local_SSAt::decrement_unwindings(int mode)
{
  if(mode==0)
  {
    assert(current_unwindings.size()>=1);
    unsigned index=current_unwindings.size()-1;
    assert(current_unwindings[index]>=1);
    current_unwindings[index]--;
  }
  else if(mode>=1)
  {
    assert(mode==1);
    current_unwindings.push_back(current_unwinding);
  }
  else // mode <=-1
  {
    for(int i=0; i>mode; --i)
      current_unwindings.pop_back();
  }
}

std::string unwindable_local_SSAt::odometer_to_string(
  const odometert &odometer, unsigned level) const
{
  if(current_unwinding<0) // not yet unwind=0
    return "";
  if(level>odometer.size())
    level=odometer.size();
  std::string unwind_suffix="";
  for(unsigned i=0; i<level; ++i)
    unwind_suffix+="%"+std::to_string(odometer[i]);
  return unwind_suffix;
}

/// overrides local_SSAt::name to add unwinder suffixes
symbol_exprt unwindable_local_SSAt::name(
  const ssa_objectt &object,
  kindt kind,
  locationt def_loc,
  locationt current_loc) const
{
  symbol_exprt s=local_SSAt::name(object, kind, def_loc);
  unsigned def_level=get_def_level(def_loc, current_loc);
  std::string unwind_suffix=
    odometer_to_string(current_unwindings, def_level);
  s.set_identifier(id2string(s.get_identifier())+unwind_suffix+suffix);

#if 0
  std::cout << "CURRENT_LOC: " << current_loc->location_number << std::endl;
  std::cout << "DEF_LOC: " << def_loc->location_number << std::endl;
  std::cout << "DEF_LEVEL: " << def_level << std::endl;
  std::cout << "RENAME_SYMBOL: "
            << object.get_identifier() << " --> "
            << s.get_identifier() << std::endl;
#endif

  return s;
}

/// returns the definition level of a variable in the loop hierarchy
unsigned unwindable_local_SSAt::get_def_level(
  locationt def_loc, locationt current_loc) const
{
  loop_hierarchy_levelt::const_iterator lhl_it=
    loop_hierarchy_level.find(def_loc);
  unsigned def_level=0;
  if(lhl_it!=loop_hierarchy_level.end())
  {
    def_level=lhl_it->second.level;
    // If a variable is defined in an other loop
    // that is defined on the same or a higher level
    // then we have to take the "merged version"
    // The reason for this is that the "exit mergers" actually
    // introduce a new SSA variable version on the context level of a loop.
    loop_hierarchy_levelt::const_iterator current_lhl=
      loop_hierarchy_level.find(current_loc);

#if 0
    std::cout << "current_location: "
              << current_loc->location_number << std::endl;
    std::cout << "parent_location: "
              <<
      (current_lhl->second.parent_loc!=goto_function.body.instructions.end()?
       current_lhl->second.parent_loc->location_number:-1)
              << std::endl;
    std::cout << "loop_number: " << lhl_it->second.loop_number << std::endl;
    std::cout << "current_number: "
              << current_lhl->second.loop_number << std::endl;
#endif

    if(current_lhl!=loop_hierarchy_level.end() &&
       current_lhl->second.level==0)
    {
      def_level=0;
    }
    else if(current_lhl!=loop_hierarchy_level.end() &&
       lhl_it->second.loop_number!=current_lhl->second.loop_number &&
       def_level>0)
    {
      bool is_parent=false;
      while(current_lhl->second.parent_loc!=
            goto_function.body.instructions.end())
      {
#if 0
        std::cout << "current-loc: "
                  << current_lhl->first->location_number << std::endl;
        std::cout << "parent-loc: "
                  << current_lhl->second.parent_loc->location_number
                  << std::endl;
        std::cout << "def_level: " << def_level << std::endl;
        std::cout << "loop_number: " << lhl_it->second.loop_number << std::endl;
        std::cout << "current_loop_number: "
                  << current_lhl->second.loop_number << std::endl;
#endif

        current_lhl=loop_hierarchy_level.find(current_lhl->second.parent_loc);
        if(lhl_it->second.loop_number==current_lhl->second.loop_number)
        {
          is_parent=true;
          break;
        }
      }
      if(!is_parent)
      {
        --def_level;
      }
    }
  }
  return def_level;
}

/// overrides local_SSAt::nondet_symbol to add unwinder suffixes
exprt unwindable_local_SSAt::nondet_symbol(
  std::string prefix,
  const typet &type,
  locationt loc,
  unsigned counter) const
{
  std::string unwind_suffix=
    odometer_to_string(current_unwindings, current_unwindings.size());
  exprt s(ID_nondet_symbol, type);
  const irep_idt identifier=
    prefix+
    std::to_string(loc->location_number)+
    "."+std::to_string(counter)+unwind_suffix+suffix;
  s.set(ID_identifier, identifier);

#if 0
  std::cout << "DEF_LOC: " << loc->location_number << std::endl;
  std::cout << "DEF_LEVEL: " << current_unwindings.size() << std::endl;
  std::cout << "RENAME_SYMBOL: "
            << s.get(ID_identifier) << std::endl;
#endif

  return s;
}

/// add unwinder suffixes
void unwindable_local_SSAt::rename(exprt &expr, locationt current_loc)
{
  if(expr.id()==ID_symbol)
  {
    symbol_exprt &s=to_symbol_expr(expr);
    locationt def_loc=goto_function.body.instructions.end();
    // we could reuse name(),
    // but then we would have to search in the ssa_objects
    // ENHANCEMENT: maybe better to attach base name, ssa name,
    //      and def_loc to the symbol_expr itself
    irep_idt id=get_ssa_name(s, def_loc);
    unsigned def_level=get_def_level(def_loc, current_loc);
    std::string unwind_suffix=
      odometer_to_string(current_unwindings, def_level);
    s.set_identifier(id2string(id)+unwind_suffix);

#if 0
    std::cout << "RENAME_SYMBOL: "
              << id << " --> "
              << s.get_identifier() << std::endl;
    std::cout << "DEF_LOC: "
              << (def_loc!=goto_function.body.instructions.end()
                  ? def_loc->location_number : -1) << std::endl;
    std::cout << "DEF_LEVEL: " << def_level << std::endl;
    std::cout << "O.size: " << current_unwindings.size() << std::endl;
    std::cout << "current: " << current_unwinding << std::endl << std::endl;
#endif
  }
  if(expr.id()==ID_nondet_symbol)
  {
    std::string unwind_suffix=
      odometer_to_string(current_unwindings, current_unwindings.size());
    std::string identifier=id2string(expr.get(ID_identifier));
    std::size_t pos=identifier.find("%");
    if(pos!=std::string::npos)
      identifier=identifier.substr(0, pos);
    expr.set(
      ID_identifier,
      identifier+unwind_suffix+suffix);
  }
  Forall_operands(it, expr)
    rename(*it, current_loc);
}

/// retrieve ssa name and location
irep_idt unwindable_local_SSAt::get_ssa_name(
  const symbol_exprt &symbol_expr, locationt &loc) const
{
  std::string s=id2string(symbol_expr.get_identifier());
#if 0
  std::cout << "id: " << s << std::endl;
#endif
  std::size_t pos2=s.find("%");
  std::size_t pos1=s.find_last_of("#");
  if(pos1==std::string::npos)
    return irep_idt(s);
  if(pos2==std::string::npos)
    pos2=s.size();
  if(s.substr(pos1+1, 2)=="lb")
    pos1+=2;
  else if(s.substr(pos1+1, 2)=="ls")
    pos1+=2;
  else if(s.substr(pos1+1, 2)=="os")
    pos1+=2;
  else if(s.substr(pos1+1, 3)=="phi")
    pos1+=3;
  else if((pos2==pos1+13) && (s.substr(pos1+1, 12)=="return_value"))
    return irep_idt(s);
#if 0
  std::cout << s << ", " << s.substr(pos1+1, pos2-pos1-1)
            << ", " << s.substr(0, pos2) << std::endl;
#endif
  loc=get_location(
    safe_string2unsigned(s.substr(pos1+1, pos2-pos1-1)));
  return irep_idt(s.substr(0, pos2));
}

/// retrieve ssa name, location, and odometer
irep_idt unwindable_local_SSAt::get_full_ssa_name(
  const symbol_exprt &symbol_expr,
  locationt &loc,
  odometert &odometer) const
{
  const std::string s=id2string(symbol_expr.get_identifier());
  std::size_t pos1=s.find("%");
  if(pos1!=std::string::npos)
  {
    std::size_t pos2=0;
    do
    {
      pos2=s.find("%", pos1+1);
      if(pos2==std::string::npos)
        pos2=s.size();
      odometer.push_back(safe_string2unsigned(s.substr(pos1+1, pos2-pos1-1)));
      pos1=pos2;
    }
    while(pos2!=s.size());
  }
  return get_ssa_name(symbol_expr, loc);
}

void unwindable_local_SSAt::compute_loop_hierarchy()
{
  loop_hierarchy_level.clear();
  std::list<goto_programt::const_targett> loopheads;
  goto_programt::const_targett i_it=goto_function.body.instructions.end();
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
      local_SSAt::locationt parent=goto_function.body.instructions.end();
      if(!loopheads.empty())
        parent=loopheads.back();
      local_SSAt::locationt loophead=i_it->get_target();
      loopheads.push_back(loophead);
      loop_hierarchy_level[loophead].loop_number=i_it->loop_number;
      loop_hierarchy_level[loophead].parent_loc=parent;
    }

    if(!loopheads.empty())
    {
      loop_hierarchy_level[i_it].loop_number=
        loop_hierarchy_level[loopheads.back()].loop_number;
      loop_hierarchy_level[i_it].level=loopheads.size();
      loop_hierarchy_level[i_it].parent_loc=
        loop_hierarchy_level[loopheads.back()].parent_loc;

#if 0
      std::cout << "- current: " <<
        loopheads.back()->location_number  << std::endl;
#endif

      if(i_it==loopheads.back())
      {
#if 0
        std::cout << "- is loop head" << std::endl;
#endif
        loopheads.pop_back();
      }
    }
  }
  while(i_it!=goto_function.body.instructions.begin());
}

void unwindable_local_SSAt::output_verbose(std::ostream &out) const
{
  for(const auto &node : nodes)
  {
    if(node.empty())
      continue;
    out << "*** " << node.location->location_number
        << " " << node.location->source_location << "\n";
    node.output(out, ns);
    for(const auto &e : node.equalities)
    {
      std::set<symbol_exprt> symbols;
      find_symbols(e, symbols);
      for(const auto &s : symbols)
      {
        if(s.type().get_bool("#dynamic"))
          out << s.get_identifier() << "\n";
      }
    }
    if(node.loophead!=nodes.end())
      out << "loop back to location "
          << node.loophead->location->location_number << "\n";
    if(!node.enabling_expr.is_true())
      out << "enabled if "
          << from_expr(ns, "", node.enabling_expr) << "\n";
    out << "\n";
  }
  out << "(enable) " << from_expr(ns, "", get_enabling_exprs()) << "\n\n";
}
