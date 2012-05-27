/*******************************************************************\

Module: Summarization

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <stack>

#include <cuddObj.hh>

#include <xml.h>

#include "transformer.h"
#include "collect_symbols.h"

class transformert
{
public:
  class locationt
  {
  public:
    // the BDD for the guard
    BDD guard;

    goto_programt::const_targett target;
    unsigned PC;
  };
  
  typedef std::vector<locationt> locationst;
  locationst locations;

  typedef std::map<goto_programt::const_targett, unsigned> location_mapt;
  location_mapt location_map;
  
  struct predicatet
  {
    irep_idt id;
    BDD var;
    exprt expr;
  };
  
  typedef std::vector<predicatet> predicatest;
  predicatest predicates;
  
  transformert(
    const namespacet &_ns,
    const goto_functionst &_goto_functions,
    Cudd &_mgr):
    ns(_ns),
    goto_functions(_goto_functions),
    mgr(_mgr)
  {
  }
  
  void operator() (const goto_functionst::goto_functiont &);
  
  void output(std::ostream &out) const;
  
protected:
  const namespacet &ns;
  const goto_functionst &goto_functions;
  Cudd &mgr;
  
  void xml(BDD, std::ostream &) const;
  
  void setup_state_map(const goto_functionst::goto_functiont &goto_function)
  {
    unsigned PC=0;
    locations.resize(goto_function.body.instructions.size());

    forall_goto_program_instructions(i_it, goto_function.body)
    {
      locations[PC].target=i_it;
      locations[PC].guard=!mgr.bddOne();
      locations[PC].PC=PC;
      location_map[i_it]=PC++;
    }
  }
  
  void discover_predicates(const goto_functionst::goto_functiont &goto_function);
  
  void make_entry_state()
  {
    assert(!locations.empty());
    locations[0].guard=mgr.bddOne();
  }
  
  std::stack<unsigned> queue;
  
  void get_successors(unsigned PC);
  
  void merge(unsigned PC, BDD guard);
};

/*******************************************************************\

Function: transformert::operator()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void transformert::operator()(const goto_functionst::goto_functiont &goto_function)
{
  setup_state_map(goto_function);
  discover_predicates(goto_function);
  if(locations.empty()) return;

  // setup entry state, and put into queue
  make_entry_state();
  queue.push(0);
  
  while(!queue.empty())
  {
    unsigned PC=queue.top();
    queue.pop();
    
    // compute successors and propagate
    get_successors(PC);
  }
}

/*******************************************************************\

Function: transformert::get_successors

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void transformert::get_successors(unsigned PC)
{
  // end of function readched?
  if(PC>=locations.size()) return;
  
  const locationt &from=locations[PC];

  const goto_programt::instructiont &instruction=
    *from.target;
    
  BDD new_guard=from.guard;
  
  if(instruction.is_goto())
  {
    merge(PC+1, new_guard);
  }
  else if(instruction.is_assign())
  {
    merge(PC+1, new_guard);
  }
  else if(instruction.is_function_call())
  {
    merge(PC+1, new_guard);
  }
  else
  {
    // treat like skip
    merge(PC+1, new_guard);
  }
}

/*******************************************************************\

Function: transformert::merge

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void transformert::merge(
  unsigned PC,
  BDD new_guard)
{
  // end of function?
  if(PC>=locations.size()) return;

  locationt &to=locations[PC];
  BDD old_guard=to.guard;
  to.guard|=new_guard; // merge
  
  if(to.guard!=old_guard)
    queue.push(PC); // fixpoint not yet reached
}

/*******************************************************************\

Function: transformert::discover_predicates

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void transformert::discover_predicates(const goto_functionst::goto_functiont &goto_function)
{
  find_symbols_sett symbols;
  collect_symbols(goto_function, symbols);
  
  predicates.resize(2);
  predicates[0].var=mgr.bddVar();
  predicates[1].var=mgr.bddVar();
}

/*******************************************************************\

Function: transformert::xml

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void transformert::xml(BDD bdd, std::ostream &out) const
{
  // dump DNF
  CUDD_VALUE_TYPE value;
  int *cube;
  DdGen *gen=bdd.FirstCube(&cube, &value);
  assert(gen!=NULL);
  assert((unsigned)mgr.ReadSize()==predicates.size());
  
  out << "  <or>" << std::endl;
  do
  {
    out << "    <and>" << std::endl;
    for(int i=0; i<mgr.ReadSize(); i++)
    {
      switch(cube[i])
      {
      case 0: // complemented
        out << "    <pred neg=\"1\" id=\"" << std::endl;
        xmlt::escape_attribute(id2string(predicates[i].id), out);
        out << "\"/>" << std::endl;
        break;

      case 1: // uncomplemented
        out << "    <pred neg=\"0\" id=\"" << std::endl;
        xmlt::escape_attribute(id2string(predicates[i].id), out);
        out << "\"/>" << std::endl;
        break;

      case 2: // don't care
        break;
        
      default:
        assert(false);
      }
    }
    out << "    </and>" << std::endl;
  }
  while(Cudd_NextCube(gen, &cube, &value)!=0);
  
  out << "  </or>" << std::endl;
}

/*******************************************************************\

Function: transformert::output

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void transformert::output(std::ostream &out) const
{
  out << "  <transformer>" << std::endl;

  // dump DNF
  xml(locations.back().guard, out);
  
  out << "  </transformer>" << std::endl;
}

/*******************************************************************\

Function: transformer

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void transformer(
  const namespacet &ns, 
  const goto_functionst &goto_functions,
  const goto_functionst::goto_functiont &goto_function,
  std::ostream &out)
{
  Cudd mgr;
  transformert transformer(ns, goto_functions, mgr);
  
  transformer(goto_function);

  transformer.output(out);
}
