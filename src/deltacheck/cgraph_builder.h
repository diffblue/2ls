/*******************************************************************\

Module: Call graph builder, builds and stores partial call graphs
(per C file).

Author: Ondrej Sery, ondrej.sery@d3s.mff.cuni.cz

\*******************************************************************/

#ifndef CPROVER_DELTACHECK_CGRAPH_BUILDER_H
#define	CPROVER_DELTACHECK_CGRAPH_BUILDER_H

#include <fstream>
#include <goto-programs/goto_functions.h>
#include <goto-programs/goto_program.h>
#include <irep.h>

#include "modular_code_analysis.h"

#define Forall_analyses(it, analyses) \
  for(analysest::iterator it=(analyses).begin(); \
      it!=(analyses).end(); ++it)
 
#define forall_analyses(it, analyses) \
  for(analysest::const_iterator it=(analyses).begin(); \
      it!=(analyses).end(); ++it)

class cgraph_buildert {
public:
  cgraph_buildert();
  ~cgraph_buildert();
  
  void analyze_module(const contextt& context,
          const goto_functionst& functions);
  void analyze_function(irep_idt current_function,
          const goto_functionst::goto_functiont& function);
  
  void add_analysis(modular_code_analysist* analysis)
  {
    analyses.push_back(analysis);
  }
  
  void add_analyses(modular_code_analysist** analyses)
  {
    while (*analyses != 0) {
      add_analysis(*analyses++);
    }
  }
  
  void serialize(const std::string& orig_file);

  void deserialize(const std::string& orig_file);
  
  void deserialize_list(std::istream& in);
  
private:
  typedef std::vector<modular_code_analysist*> analysest;
  
  analysest analyses;
  
  void print_analyses(std::ostream& out) const;
  void compute_fixpoints();
  void remove_invisible();
};

#endif

