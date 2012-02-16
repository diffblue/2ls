/*******************************************************************\

Module: Call graph builder, builds and stores partial call graphs
(per C file).

Author: Ondrej Sery, ondrej.sery@d3s.mff.cuni.cz

\*******************************************************************/

#include <context.h>
#include <string>
#include <iostream>

#include "cgraph_builder.h"

cgraph_buildert::cgraph_buildert()
{
}

cgraph_buildert::~cgraph_buildert()
{
}

void
cgraph_buildert::analyze_module(const contextt& context, 
        const goto_functionst& functions) 
{
  Forall_analyses(it, analyses)
  {
    (*it)->set_context(context);
  }
  
  forall_goto_functions(it, functions) 
  {
    const goto_functionst::goto_functiont& function = it->second;
    
    if (function.body_available) 
    {
      std::cout << "=================================" << std::endl;
      std::cout << "Analyzing function: " << it->first << std::endl;
      analyze_function(it->first, function);
    }
  }
  
  std::cout << "===== AFTER COLLECTION =====" << std::endl;
  print_analyses(std::cout);
  
  compute_fixpoints();
  
  std::cout << "===== AFTER FIXPOINT =====" << std::endl;
  print_analyses(std::cout);
  
  remove_invisible();
  
  std::cout << "===== AFTER FILTERING =====" << std::endl;
  print_analyses(std::cout);
}

void
cgraph_buildert::analyze_function(
        irep_idt current_function,
        const goto_functionst::goto_functiont& function)
{
  Forall_analyses(it, analyses)
  {
    (*it)->enter_function(current_function);
    forall_goto_program_instructions(it2, function.body)
    {
      (*it)->visit(*it2);
    }
    (*it)->exit_function();
  }
}

void 
cgraph_buildert::print_analyses(std::ostream& out) const
{
  forall_analyses(it, analyses)
  {
    out << " *** Analysis: " << (*it)->get_analysis_id() << std::endl;
    (*it)->print(out);
    out << std::endl;
  }
}

void
cgraph_buildert::compute_fixpoints()
{
  Forall_analyses(it, analyses)
  {
    (*it)->compute_fixpoint();
  }
}

void
cgraph_buildert::remove_invisible()
{
  Forall_analyses(it, analyses)
  {
    (*it)->remove_invisible();
  }
}

void
cgraph_buildert::serialize(const std::string& orig_file)
{
  forall_analyses(it, analyses)
  {
    std::string analysis_file = orig_file + (*it)->get_default_suffix();
    std::ofstream out(analysis_file.c_str());
    if (!out)
      throw "Failed to write partial analysis result: " + analysis_file;

    (*it)->serialize(out);

    if (!out) {
      out.close();
      throw "Failed to write the partial call graph file: " + analysis_file;
    }
    out.close();
  }
}

void
cgraph_buildert::deserialize(const std::string& orig_file)
{
  Forall_analyses(it, analyses)
  {
    std::string analysis_file = orig_file + (*it)->get_default_suffix();
    std::ifstream in(analysis_file.c_str());
    if (!in)
      throw "Failed to read the partial call graph file: " + analysis_file;

    (*it)->deserialize(in);

    if (!in)
    {
      in.close();
      throw "Failed to read the partial call graph file: " + analysis_file;
    }
    in.close();
  }
}

void
cgraph_buildert::deserialize_list(std::istream& in)
{
  std::string line_str;
  
  while (getline(in, line_str))
  {
    if (!line_str.empty())
      deserialize(line_str);
  }
  
  if (in.bad())
  {
    throw "Failed to read the list of call graph files.";
  }
  
  std::cout << "===== AFTER LOAD =====" << std::endl;
  print_analyses(std::cout);
  compute_fixpoints();
  std::cout << "===== AFTER FIXPOINT =====" << std::endl;
  print_analyses(std::cout);
}
