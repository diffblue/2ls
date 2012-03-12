/*******************************************************************\

Module: Ancestor of modular (i.e., per C file) fixpoint analysis 
of goto-programs.

Author: Ondrej Sery, ondrej.sery@d3s.mff.cuni.cz

\*******************************************************************/

#include "modular_code_analysis.h"

modular_code_analysist::modular_code_analysist() : context(NULL)
{
}

modular_code_analysist::~modular_code_analysist() 
{
}

void
modular_code_analysist::visit(const goto_programt::instructiont& instr)
{
  switch(instr.type) {
    case ASSUME:
      accept_assume(to_code_assume(instr.code));
      break;
    case ASSIGN:
      accept_assign(to_code_assign(instr.code));
      break;
    case ASSERT:
      accept_assert(to_code_assert(instr.code));
      break;
    case FUNCTION_CALL:
      accept_function_call(to_code_function_call(instr.code));
      break;
    case RETURN:
      accept_return(to_code_return(instr.code));
      break;
    case SKIP: // fall through
    case DECL: // fall through
    case GOTO: // fall through
    case END_FUNCTION: // fall through
      break;
    default:
      throw "Unexpected instruction type in modular_code_analysist::visit()";
      break;
  }
}

void
modular_code_analysist::print(std::ostream& out) const 
{
  // Values
  for (value_mapt::const_iterator it = value_map.begin();
          it != value_map.end();
          ++it)
  {
    out << "Values for \"" << it->first << "\" <--" << std::endl;

    const valuest& values = it->second;
    for (valuest::const_iterator it2 = values.begin();
            it2 != values.end();
            ++it2)
    {
      out << "    \"" << *it2 << "\"" << std::endl;
    }
  }
  // Rules
  for (rulest::const_iterator it = rules.begin();
          it != rules.end();
          ++it)
  {
    out << "Rules for \"" << it->first << "\" <--" << std::endl;

    const variablest& variables = it->second;
    for (variablest::const_iterator it2 = variables.begin();
            it2 != variables.end();
            ++it2)
    {
      out << "    \"" << *it2 << "\"" << std::endl;
    }
  }
}
  
void
modular_code_analysist::serialize(std::ostream& out) const 
{
  // Values
  out << value_map.size() << std::endl;
  for (value_mapt::const_iterator it = value_map.begin();
          it != value_map.end();
          ++it) 
  {
    const valuest& values = it->second;

    out << it->first << std::endl;
    out << values.size() << std::endl;

    for (valuest::const_iterator it2 = values.begin();
            it2 != values.end();
            ++it2) 
    {
      out << *it2 << std::endl;
    }
  }
  // Rules
  out << rules.size() << std::endl;
  for (rulest::const_iterator it = rules.begin();
          it != rules.end();
          ++it) 
  {
    const variablest& variables = it->second;
    out << it->first << std::endl;
    out << it->second.size() << std::endl;

    for (variablest::const_iterator it2 = variables.begin();
            it2 != variables.end();
            ++it2) 
    {
      out << *it2 << std::endl;
    }
  }
  // Visible variables
  out << visible_variables.size() << std::endl;
  for (variablest::const_iterator it = visible_variables.begin();
          it != visible_variables.end();
          ++it) 
  {
    out << *it << std::endl;
  }
}
  
void
modular_code_analysist::deserialize(std::istream& in) 
{
  // Values
  int values_map_size;
  in >> values_map_size;
  if (!in.good()) return;

  for (int i = 0; i < values_map_size; ++i) 
  {
    int values_size;
    std::string var_str;
    in >> var_str;
    in >> values_size;
    variablet var(var_str);
    if (!in.good()) return;

    for (int j = 0; j < values_size; ++j) 
    {
      std::string val_str;
      in >> val_str;
      valuet val(val_str);

      add_value(var, val);
    }
  }
  // Rules
  int rules_size;
  in >> rules_size;
  if (!in.good()) return;

  for (int i = 0; i < rules_size; ++i) 
  {
    int vars_size;
    std::string var_str;
    in >> var_str;
    in >> vars_size;
    variablet var(var_str);
    if (!in.good()) return;

    for (int j = 0; j < vars_size; ++j) 
    {
      std::string var2_str;
      in >> var2_str;
      variablet var2(var2_str);

      add_rule(var, var2);
    }
  }
  // Visible variables
  int visible_size;
  in >> visible_size;
  if (!in.good()) return;

  for (int i = 0; i < visible_size; ++i) 
  {
    std::string var_str;
    in >> var_str;
    variablet var(var_str);

    set_visible(var);
  }
}

