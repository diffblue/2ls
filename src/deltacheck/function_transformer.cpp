/*******************************************************************\

Module: Summarization

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <stack>

#include <cuddObj.hh>

#include <xml.h>

#include "function_transformer.h"
#include "statement_transformer.h"
#include "collect_symbols.h"
#include "discover_predicates.h"
#include "predicates.h"

class function_transformert
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
  
  predicatest predicates;
  
  function_transformert(
    const namespacet &_ns,
    const goto_functionst &_goto_functions,
    Cudd &_mgr,
    message_handlert &_message_handler):
    ns(_ns),
    goto_functions(_goto_functions),
    mgr(_mgr),
    message(_message_handler)
  {
  }
  
  void operator() (const goto_functionst::goto_functiont &);
  
  void output(std::ostream &out) const;
  
protected:
  const namespacet &ns;
  const goto_functionst &goto_functions;
  Cudd &mgr;
  messaget message;
  
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
  
  void add(const std::list<exprt> &);
  
  void discover_predicates(
    const goto_functionst::goto_functiont &goto_function);
  
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

Function: function_transformert::operator()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void function_transformert::operator()(
  const goto_functionst::goto_functiont &goto_function)
{
  setup_state_map(goto_function);
  discover_predicates(goto_function);
  
  std::string m="Predicates: ";
  for(predicatest::const_iterator p_it=predicates.begin();
      p_it!=predicates.end();
      p_it++)
  {
    if(p_it!=predicates.begin()) m+=", ";
    m+=from_expr(ns, "", p_it->expr);
  }
  message.debug(m);

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

Function: function_transformert::get_successors

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void function_transformert::get_successors(unsigned PC)
{
  // end of function readched?
  if(PC>=locations.size()) return;
  
  const locationt &from=locations[PC];

  const goto_programt::instructiont &instruction=
    *from.target;
    
  statement_transformert statement_transformer(predicates, mgr, ns);

  if(instruction.is_goto())
  {
    // guarded?
    if(instruction.guard.is_false())
      merge(PC+1, from.guard);
    else
    {
      if(!instruction.guard.is_true())
      {
        BDD new_guard=
          statement_transformer.guard_not(from.guard, instruction.guard);
        merge(PC+1, new_guard);
      }
      
      // targets
      for(goto_programt::instructiont::targetst::const_iterator
          it=instruction.targets.begin();
          it!=instruction.targets.end();
          it++)
      {
        BDD new_guard=
          statement_transformer.guard(from.guard, instruction.guard);
        //merge(PC+1, new_guard);
      }
    }
  }
  else if(instruction.is_assign())
  {
    const code_assignt &code_assign=to_code_assign(instruction.code);
    BDD new_guard=
      statement_transformer.assign(from.guard, code_assign);
    merge(PC+1, new_guard);
  }
  else if(instruction.is_function_call())
  {
    BDD new_guard=from.guard;
    merge(PC+1, new_guard);
  }
  else if(instruction.is_assume())
  {
    BDD new_guard=
      statement_transformer.guard(new_guard, instruction.guard);

    merge(PC+1, new_guard);
  }
  else if(instruction.is_assert())
  {
    BDD new_guard=from.guard;
    merge(PC+1, new_guard);
  }
  else if(instruction.is_other())
  {
    BDD new_guard=from.guard;
    merge(PC+1, new_guard);
  }
  else if(instruction.is_start_thread())
  {
    // targets
    for(goto_programt::instructiont::targetst::const_iterator
        it=instruction.targets.begin();
        it!=instruction.targets.end();
        it++)
    {
      BDD new_guard=
        statement_transformer.guard(new_guard, instruction.guard);
      //merge(PC+1, new_guard);
    }
  }
  else if(instruction.is_end_thread())
  {
    // no successor
  }
  else if(instruction.is_end_function())
  {
    // no successor
  }
  else if(instruction.is_atomic_begin())
  {
    BDD new_guard=from.guard;
    merge(PC+1, new_guard);
  }
  else if(instruction.is_atomic_end())
  {
    BDD new_guard=from.guard;
    merge(PC+1, new_guard);
  }
  else if(instruction.is_return())
  {
    BDD new_guard=from.guard;
    // process return value
  
    // go to end-of-function
    merge(locations.size()-1, new_guard);
  }
  else if(instruction.is_decl())
  {
    BDD new_guard=from.guard;
    merge(PC+1, new_guard);
  }
  else if(instruction.is_dead())
  {
    BDD new_guard=from.guard;
    merge(PC+1, new_guard);
  }
  else if(instruction.is_throw())
  {
    // complex successor
  }
  else if(instruction.is_catch())
  {
    BDD new_guard=from.guard;
    merge(PC+1, new_guard);
  }
  else if(instruction.is_skip() ||
          instruction.is_location())
  {
    merge(PC+1, from.guard);
  }
  else
  {
    // treat like skip
    merge(PC+1, from.guard);
  }
}

/*******************************************************************\

Function: function_transformert::merge

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void function_transformert::merge(
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

Function: function_transformert::add

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void function_transformert::add(
  const std::list<exprt> &new_predicates)
{
  for(std::list<exprt>::const_iterator
      it=new_predicates.begin();
      it!=new_predicates.end();
      it++)
  {
    unsigned index=predicates.size();
  
    predicates.push_back(predicatet());
    predicates.back().expr=*it;
    
    // this will cause the ordering of the variable and
    // it's next-state version to be interleaved
    predicates.back().var=mgr.bddVar(index*2);
    predicates.back().next_var=mgr.bddVar(index*2+1);
  }
}

/*******************************************************************\

Function: function_transformert::discover_predicates

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void function_transformert::discover_predicates(
  const goto_functionst::goto_functiont &goto_function)
{
  forall_goto_program_instructions(i_it, goto_function.body)
  {
    const goto_programt::instructiont &instruction=*i_it;
  
    if(instruction.is_assert())
    {
      add(::discover_predicates(instruction.guard, ns));
    }
  }
}

/*******************************************************************\

Function: function_transformert::xml

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void function_transformert::xml(BDD bdd, std::ostream &out) const
{
  // dump DNF
  CUDD_VALUE_TYPE value;
  int *cube;
  DdGen *gen=bdd.FirstCube(&cube, &value);
  assert(gen!=NULL);
  assert((unsigned)mgr.ReadSize()>=predicates.size()*2);
  
  out << "  <or>" << std::endl;
  do
  {
    out << "    <and>" << std::endl;
    for(int i=0; i<mgr.ReadSize(); i++)
    {
      unsigned p=i/2;
      
      if(cube[i]!=2)
        assert((i%2)==0);
    
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

Function: function_transformert::output

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void function_transformert::output(std::ostream &out) const
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

void function_transformer(
  const namespacet &ns, 
  const goto_functionst &goto_functions,
  const goto_functionst::goto_functiont &goto_function,
  message_handlert &message_handler,
  std::ostream &out)
{
  Cudd mgr;
  function_transformert function_transformer(
    ns, goto_functions, mgr, message_handler);
  
  function_transformer(goto_function);

  function_transformer.output(out);
}
