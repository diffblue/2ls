/*******************************************************************
 Module: SSA Unwinder

 Author: Saurabh Joshi

 \*******************************************************************/

#include <iostream>

#include <util/i2string.h>
#include <util/string2int.h>
#include <limits>
#include <cstdlib>

#include "ssa_unwinder.h"


void ssa_local_unwindert::set_return_var(const irep_idt& id)
{
  return_var="c::"+id2string(id)+"#return_value";
}
std::string ssa_local_unwindert::keep_first_two_hash(const std::string& str) const
{
   std::size_t pos = str.find('#');
   if(pos==std::string::npos) return str;
   pos=str.find('#',pos+1);
   if(pos==std::string::npos) return str;
   return str.substr(0,pos);
}
void ssa_local_unwindert::dissect_loop_suffix(const irep_idt& id,
    irep_idt& before_suffix,std::list<unsigned>& iterations,bool baseonly) const
{
    std::string s = id2string(id);

    std::size_t pos=s.find_first_of("%");
    if(pos==std::string::npos) { return;     }

    before_suffix=s.substr(0,pos);
    if(baseonly) return;
    std::size_t pos1;

    do
    {
      pos1=s.find_first_of("%",pos+1);
      if(pos1==std::string::npos) continue;
     // if(pos1==pos+1) {assert(false&& "Ill formed loop suffix");}
      //TODO use safe string to unsigned

      iterations.push_back(string2integer(s.substr(pos+1,pos1-(pos+1)),10).to_ulong());
      pos=pos1;

    }while(pos1!=std::string::npos);

    //if(pos==(s.length()-1)) {assert(false && "Ill-formed loop suffix");}

    iterations.push_back(string2integer(s.substr(pos+1)).to_ulong());

}
/*****************************************************************************
 *
 *  Function : ssa_local_unwindert::get_base_name
 *
 *  Input : id - symbol name
 *
 *  Output : irep_id - a symbol name which is stripped off of all suffixes
 *            beginnign with the first #
 *
 *****************************************************************************/
irep_idt ssa_local_unwindert::get_base_name(const irep_idt& id)
{
  std::string s = id2string(id);
  std::size_t pos = s.find("#");
  if(pos==std::string::npos) {return id;}
  std::string s1=s.substr(0,pos);
  return irep_idt(s1);
}
void ssa_local_unwindert::is_void_func()
{
  for (local_SSAt::objectst::const_iterator o_it =
           SSA.ssa_objects.objects.begin();
         o_it != SSA.ssa_objects.objects.end(); o_it++) {

    if(as_string(o_it->get_identifier()).find(RETVAR)){ isvoid=false; return;}
  }
 isvoid=true;

}
/*****************************************************************************\
 *
 * Function : ssa_local_unwindert::ssa_local_unwindert
 *
 * Input : _SSA - a reference to an object of type local_SSAt
 *
 * Output :
 *
 * Purpose : This just initialises the reference and does nothing else. A
 *            separate initialier init() is provided to populate the
 *            hierarchical loop
 *            data structure
 *
 *
 *****************************************************************************/
ssa_local_unwindert::ssa_local_unwindert(local_SSAt& _SSA,bool k_induct,
    bool _ibmc):isvoid(true), SSA(_SSA),
    current_unwinding(0),prev_unwinding(std::numeric_limits<unsigned int>::max()),
    is_initialized(false),is_kinduction(k_induct),
    is_ibmc(_ibmc){ }
/*******************************************************************
 Struct: compare_node_iterators

 Inputs:

 Outputs:

 Purpose: a function object to pass as a comparator for std::set
 to enable us to order iterators. It takes the address of the
 object being pointed to by iterators and compared them as
 unsigned long

 \*******************************************************************/
bool compare_node_iteratorst::operator()(const local_SSAt::nodest::iterator& a,
    const local_SSAt::nodest::iterator& b) const {
  return ((unsigned long) (&(*a)) < (unsigned long) (&(*b)));
}
bool compare_node_iteratorst::operator()(const local_SSAt::nodest::const_iterator& a,
    const local_SSAt::nodest::const_iterator& b) const {
  return ((unsigned long) (&(*a)) < (unsigned long) (&(*b)));
}
/*****************************************************************************\
 * Function : ssa_local_unwindert::init
 *
 * Inputs : None
 *
 * Outputs : None
 *
 * Purpose : from local_SSA, construct a hierarchical tree_loopnodet rooted at
 * root_node. loophead of a loop is always stored as the first node in
 * body_nodes. A backedge node is always the last node in body_nodes.
 *  A nested loop is stored as a tree_loopnodet in loop_nodes
 *
 *****************************************************************************/

void ssa_local_unwindert::init() {
  std::set<local_SSAt::nodest::iterator, compare_node_iteratorst> loopheads;

  loopheads.clear();
  for (local_SSAt::nodest::iterator n_it = SSA.nodes.begin();
       n_it != SSA.nodes.end(); n_it++) {
    //continue until a back-edge is found
    if (n_it->loophead == SSA.nodes.end())
      continue;
    // all the loop-head nodes must be inserted
    assert(loopheads.insert(n_it->loophead).second);
  }

  if (loopheads.empty()) {
    is_initialized = true;
    loopless = true;
    return;
  }

  loopless = false;
  tree_loopnodet* current_node = NULL;

  std::list<tree_loopnodet*> current_stack;
  current_stack.push_back(&root_node);
  current_node = current_stack.back();
  for (local_SSAt::nodest::iterator n_it = SSA.nodes.begin();
       n_it != SSA.nodes.end(); n_it++) {
    if (loopheads.find(n_it) != loopheads.end()) {
      //we've found a loop-head, so create a
      //tree_loopnodet for the nested loop
      current_node = new tree_loopnodet();
      current_stack.push_back(current_node);
      current_node = current_stack.back();
      // ASSUME : first node in body_nodes is always the
      // loop-head of the loop except root_node
#if 0
      //get the guard for the loophead to be reachable
      //get the loop condition
      current_node->entry_guard=SSA.guard_symbol(n_it->location);
      current_node->cond_expr=SSA.cond_symbol(n_it->location);
#endif
      current_node->body_nodes.push_back(*n_it);
      current_node->body_nodes.back().marked = false;

#if 0
      {
        //compute pre_post_exprs for the current loop

        const ssa_domaint::phi_nodest &phi_nodes =
	  SSA.ssa_analysis[n_it->location].phi_nodes;

        for(local_SSAt::objectst::const_iterator
	      o_it=SSA.ssa_objects.objects.begin();
            o_it!=SSA.ssa_objects.objects.end();
            o_it++)
        {
          ssa_domaint::phi_nodest::const_iterator p_it =
	    phi_nodes.find(o_it->get_identifier());

          if(p_it==phi_nodes.end()) continue; // object not modified in this loop

          symbol_exprt pre =
	    SSA.name(*o_it, local_SSAt::LOOP_BACK, n_it->location);
          symbol_exprt post = SSA.read_rhs(*o_it, n_it->location);

          current_node->pre_post_exprs[pre] = post;
          std::cout << pre << "  ---" << post << std::endl;
        }
      }
#endif
    } else if (n_it->loophead != SSA.nodes.end()) {
      //we've found the end of the loop so move
      // up the stack

      //ASSUME : the last node in the body_nodes
      // of a loop is always the back-edge node
      //copy assertions after the loop for assertion hoisting
      current_node->assertions_after_loop = n_it->loophead->assertions_after_loop;
      current_node->body_nodes.push_back(*n_it);
      current_node->body_nodes.back().marked = false;

      //reset the back-edge
      current_node->body_nodes.rbegin()->loophead=SSA.nodes.end();

      {
        local_SSAt::nodet loophead = current_node->body_nodes.front();
	loophead.marked = false;
        //compute pre_post_exprs for the current loop

        const ssa_domaint::phi_nodest &phi_nodes =
	  SSA.ssa_analysis[loophead.location].phi_nodes;

        for (local_SSAt::objectst::const_iterator o_it =
	       SSA.ssa_objects.objects.begin();
	     o_it != SSA.ssa_objects.objects.end(); o_it++) {
          ssa_domaint::phi_nodest::const_iterator p_it = phi_nodes.find(
	    o_it->get_identifier());

          if (p_it == phi_nodes.end())
            continue; // object not modified in this loop
          //capture which variables are modified
          //this will be used during renaming
          current_node->vars_modified.insert(o_it->get_identifier());


          symbol_exprt pre = SSA.name(*o_it, local_SSAt::LOOP_BACK,
				      n_it->location);
          symbol_exprt post = SSA.read_rhs(*o_it, n_it->location);

          current_node->pre_post_exprs[pre] = post;

        }
      }

#if 0
      //get the guard at the end of the loop body
      //this guard needs to be fed to the next iteration
      current_node->exit_guard=SSA.guard_symbol(n_it->location);
#endif
      assert(!current_stack.empty());
      //assert would fail for unstructured program
      current_stack.pop_back();

      tree_loopnodet* new_current_node = current_stack.back();
      //hope push_back does a copy by value - yes it does
      new_current_node->loop_nodes.push_back(*current_node);

      delete current_node;


      current_node = new_current_node;
    } else {
      //a normal node belongs to body_nodes of the current loop
      current_node->body_nodes.push_back(*n_it);
      current_node->body_nodes.back().marked=false;
    }

  }
  //only the top level body_nodes are required
  // all other required nodes will be inserted during unwinding
  // so avoid duplicates by removing them from SSA.nodes
  SSA.nodes.clear();
  SSA.nodes.insert(SSA.nodes.begin(), root_node.body_nodes.begin(),
		   root_node.body_nodes.end());

  populate_parents();
  is_void_func();

    if(!isvoid)
    {
    populate_return_val_mod();
    }

  //populate connector for every loop
  for(loop_nodest::iterator lit=root_node.loop_nodes.begin();
      lit!=root_node.loop_nodes.end();lit++)
  {
    populate_connectors(*lit);
  }

  put_varmod_in_parent();
#if 0
  //pointers of tree_loopnodet are stable now and they must not be
  //modified beyond this point. Now populate "parent" field of
  //every node
  std::list<tree_loopnodet*> worklist;
  worklist.push_back(&root_node);
  while(!worklist.empty())
  {
    tree_loopnodet* current_node = worklist.back();
    worklist.pop_back();

    if(current_node->loop_nodes.empty()) continue;
    for(loop_nodest::iterator it=current_node->loop_nodes.begin();
        it!=current_node->loop_nodes.end();it++)
    {
      it->parent = current_node;
#if 1
      // if a variable is modified in child loop then consider it modified
      //for the current loop for the purpose of renaming
      //NOTE : this code only looks at the child. Not sure if you should look at
      // all the descendents for the purpose of renaming
      current_node->vars_modified.insert(it->vars_modified.begin(),it->vars_modified.end());
#endif
      worklist.push_back(&(*it));
    }

  }

#endif
  is_initialized=true;

}
void ssa_local_unwindert::propagate_varmod_to_ancestors(const irep_idt& id,tree_loopnodet* current_loop)
{
  current_loop->vars_modified.insert(id);
  if(current_loop->parent!=NULL && current_loop->parent!=&root_node)
  {
    propagate_varmod_to_ancestors(id,current_loop->parent);
  }
}

void ssa_local_unwindert::populate_parents()
{
  std::list<tree_loopnodet*> worklist;
   worklist.push_back(&root_node);
   while(!worklist.empty())
   {
     tree_loopnodet* current_node = worklist.back();
     worklist.pop_back();

     if(current_node->loop_nodes.empty()) continue;
     for(loop_nodest::iterator it=current_node->loop_nodes.begin();
         it!=current_node->loop_nodes.end();it++)
     {
       it->parent = current_node;

       worklist.push_back(&(*it));
     }

   }
}
void ssa_local_unwindert::put_varmod_in_parent()
{
  std::list<tree_loopnodet*> worklist;
   worklist.push_back(&root_node);
   while(!worklist.empty())
   {
     tree_loopnodet* current_node = worklist.back();
     worklist.pop_back();

     if(current_node->loop_nodes.empty()) continue;
     for(loop_nodest::iterator it=current_node->loop_nodes.begin();
         it!=current_node->loop_nodes.end();it++)
     {


       // if a variable is modified in child loop then consider it modified
       //for the current loop for the purpose of renaming
       //NOTE : this code only looks at the child. Not sure if you should look at
       // all the descendents for the purpose of renaming
       current_node->vars_modified.insert(it->vars_modified.begin(),it->vars_modified.end());
       worklist.push_back(&(*it));
     }

   }
}
void ssa_local_unwindert::populate_return_val_mod()
{
  std::list<tree_loopnodet*> worklist;
  for(loop_nodest::iterator lit=root_node.loop_nodes.begin();
      lit!=root_node.loop_nodes.end();lit++)
  {
    worklist.push_back(&(*lit));
  }

while(!worklist.empty())
{
  tree_loopnodet* current_loop=worklist.back();
  worklist.pop_back();
  for(local_SSAt::nodest::iterator nit=current_loop->body_nodes.begin();
      nit!=current_loop->body_nodes.end();nit++)
  {
      for(local_SSAt::nodet::equalitiest::iterator eit=nit->equalities.begin();
          eit!=nit->equalities.end();eit++)
      {

        if(eit->lhs().id()==ID_symbol)
        {

          symbol_exprt sym_e=to_symbol_expr(eit->lhs());
          irep_idt sym_id=sym_e.get_identifier();
          std::string s = as_string(sym_id);

          std::size_t pos=s.find(RETVAR);
          if(pos!=std::string::npos)
          {

              irep_idt id= keep_first_two_hash(s);
            propagate_varmod_to_ancestors(id,current_loop);
              current_loop->return_nodes.insert(nit);
          }
        }
      }
  }
  for(loop_nodest::iterator lit=current_loop->loop_nodes.begin();
      lit!=current_loop->loop_nodes.end();lit++)
  {
    worklist.push_back(&(*lit));
  }
}

}
void ssa_local_unwindert::populate_connectors(tree_loopnodet& current_loop)
{
  typedef std::map<irep_idt,local_SSAt::objectst::iterator> varobj_mapt;
  varobj_mapt varobj_map;
  body_nodest::const_iterator it=current_loop.body_nodes.begin();

  body_nodest::const_reverse_iterator lit = current_loop.body_nodes.rbegin();

  std::vector<exprt> exit_conditions;

    unsigned int end_location = lit->location->location_number;


        for(local_SSAt::nodet::equalitiest::const_iterator eqit=lit->equalities.begin();
            eqit!=lit->equalities.end();eqit++)
        {
           if(eqit->lhs()==SSA.cond_symbol(lit->location))
           {
              if(!eqit->rhs().is_true())
           {
             current_loop.is_dowhile=true;

           }
            break;
           }
        }
        exprt cond_e;
        exprt guard_e;
        exprt loop_continue_e;
        if(!current_loop.is_dowhile)
        {
           cond_e = SSA.cond_symbol(it->location);
           guard_e=SSA.guard_symbol(it->location);
           exit_conditions.push_back(cond_e);
           //either you reached head of the loop and exit
           //or you have not reached the end of the loop
           //this will happen only for while. What about dowhile?
           loop_continue_e = and_exprt(cond_e,guard_e);
            loop_continue_e=or_exprt(loop_continue_e,not_exprt(SSA.guard_symbol(lit->location)));
        }
        else
        {
           cond_e = SSA.cond_symbol(lit->location);
           guard_e=SSA.guard_symbol(lit->location);
           exprt not_cond_e=not_exprt(cond_e);
           exit_conditions.push_back(not_cond_e);
           loop_continue_e=and_exprt(not_cond_e,guard_e);
         }

  for (local_SSAt::objectst::const_iterator o_it =
               SSA.ssa_objects.objects.begin();
             o_it != SSA.ssa_objects.objects.end(); o_it++)
      {
        std::set<irep_idt>::const_iterator fit = current_loop.vars_modified.find(o_it->get_identifier());
        if(fit==current_loop.vars_modified.end()) continue;

        varobj_map[*fit]=o_it;
        //though #return_value is added into vars_modified
        //we don't want PHI connectors for them
        if(as_string(*fit).find(RETVAR)!=std::string::npos) continue;

        if(!current_loop.is_dowhile)
        {
         current_loop.connectors.insert(exp_guard_cond_pairt(SSA.name(*o_it,local_SSAt::PHI,it->location),loop_continue_e));
        }
        else
        {
          current_loop.connectors.insert(exp_guard_cond_pairt(SSA.read_rhs(*o_it,lit->location),loop_continue_e));
        }
      }

if(!current_loop.is_dowhile)
{
  current_loop.connectors.insert(exp_guard_cond_pairt(SSA.guard_symbol(it->location),loop_continue_e));
  current_loop.connectors.insert(exp_guard_cond_pairt(SSA.cond_symbol(it->location),loop_continue_e));
}
else
{
  current_loop.connectors.insert(exp_guard_cond_pairt(SSA.guard_symbol(lit->location),loop_continue_e));
  current_loop.connectors.insert(exp_guard_cond_pairt(SSA.cond_symbol(lit->location),loop_continue_e));
}
//since loophead is processed we can probably go on?
it++;


for(;it!=current_loop.body_nodes.end();it++)
{
  body_nodest::const_iterator next_node = it; next_node++;
  if(next_node==current_loop.body_nodes.end()) break;

  if(!is_break_node(*it,end_location)) continue;
  //no separete treatment for return nodes required as break nodes
  // are all nodes with jump out of the loop which include the return
  //nodes
  exprt break_cond_e=SSA.cond_symbol(it->location);
  //NOTE : do we check if the end of the guard has reached in loop_continue_e?
loop_continue_e = and_exprt(break_cond_e,SSA.guard_symbol(it->location));
if(is_return_node(current_loop,it))
{
exit_conditions.push_back(break_cond_e);
}

  for(varobj_mapt::iterator vit=varobj_map.begin();vit!=varobj_map.end();vit++)
  {
    if(it==current_loop.body_nodes.begin() &&
        (as_string(vit->first).find(RETVAR)!=std::string::npos)) continue;

    current_loop.connectors.insert(exp_guard_cond_pairt(SSA.read_rhs(*(vit->second),it->location),loop_continue_e));
    current_loop.connectors.insert(exp_guard_cond_pairt(SSA.guard_symbol(it->location),loop_continue_e));
    current_loop.connectors.insert(exp_guard_cond_pairt(SSA.cond_symbol(it->location),loop_continue_e));
  }


}

current_loop.exit_condition=disjunction(exit_conditions);

for(loop_nodest::iterator loopit=current_loop.loop_nodes.begin();
    loopit!=current_loop.loop_nodes.end();loopit++)
{
  populate_connectors(*loopit);
}

}

bool ssa_local_unwindert::is_break_node(const local_SSAt::nodet& node,
    const unsigned int end_location) const
{
  local_SSAt::locationt instr = node.location;
  if(!instr->is_goto()) return false;

  // a break should have only one target
  if(instr->targets.size()>1) return false;

  if(instr->targets.front()->location_number <= end_location ) return false;
  return true;

}

bool ssa_local_unwindert::is_return_node(const tree_loopnodet& current_loop,
    const local_SSAt::nodest::const_iterator& node) const
{
  return_nodest::const_iterator it=current_loop.return_nodes.find(node);
  return (it!=current_loop.return_nodes.end());
}
/*****************************************************************************\
 * Function : ssa_local_unwindert::unwind
 *
 * Input : k - unwind_depth
 *
 * Output : new nodes added to reflect incremental unwinding
 *
 * Purpose : for all the loops at root-level call unwinder to do
 *           incremental unwinding
 * Pre condition : k must be greater than current_unwinding
 *
 *****************************************************************************/
void ssa_local_unwindert::unwind(const irep_idt& fname,unsigned int k) {
  assert(is_initialized);
  if (loopless)
    return;
  if (k <= current_unwinding)
    assert(false && "unwind depth smaller than previous unwinding!!");

//watch out for border-line cases
  //parameter to unwind must never be 0
    prev_unwinding=current_unwinding;

  local_SSAt::nodest new_nodes;
  irep_idt func_name = "unwind:"+as_string(fname)+":enable_"+i2string(k);
 /* if(return_var.empty())
  {
   return_var=as_string(fname)+"#return_value";
  }*/
  symbol_exprt new_sym(func_name,bool_typet());
  SSA.enabling_exprs.push_back(new_sym);
  for (loop_nodest::iterator it = root_node.loop_nodes.begin();
       it != root_node.loop_nodes.end(); it++) {
    unwind(*it, "", false, k, new_sym,new_nodes);
  }
//commit all the nodes
  SSA.nodes.splice(SSA.nodes.begin(), new_nodes);
  current_unwinding = k;


}
/*****************************************************************************\
 *
 *  Function : ssa_local_unwindert::need_renaming
 *
 *  Input : current_loop - the current context of renaming,
 *             id - id to be renamed
 *
 *  Output : bool - If id needs to be renamed within current context
 *
 *  Purpose : If a symbol starts with "$cond" or "$guard" it will always have
 *              to be renamed in the current context. If the variable
 *              is modified in the current context (loop) then also it has to
 *              be renamed
 *
 *****************************************************************************/
int ssa_local_unwindert::need_renaming(tree_loopnodet& current_loop,
    const irep_idt& id)
{

  //irep_idt base_id = get_base_name(id);
modvar_levelt::iterator mit = current_loop.modvar_level.find(id);
  if(mit!=current_loop.modvar_level.end())
  {
    return mit->second;
  }

  //std::string s = id2string(base_id);
 // if(s.find("$cond")!=std::string::npos) return true;
 // if(s.find("$guard")!=std::string::npos) return true;
  if(current_loop.vars_modified.find(id)!=current_loop.vars_modified.end())
    {

     current_loop.modvar_level[id]=0;
     return 0;

    }

    if(current_loop.parent==NULL || current_loop.parent==&root_node) {  current_loop.modvar_level[id]=-1; return -1;}
    int mylevel = need_renaming(*current_loop.parent,id);
    if(mylevel < 0) { current_loop.modvar_level[id]=-1; return -1;}
    current_loop.modvar_level[id] = mylevel+1;
    return mylevel+1;



}

unsigned int ssa_local_unwindert::get_last_iteration(std::string& suffix, bool& result)
{
  std::size_t pos = suffix.find_last_of("%");
  if(pos==std::string::npos) {result=false; return 0;}
   unsigned int val = safe_string2unsigned(suffix.substr(pos+1));
   assert(val < std::numeric_limits<unsigned int>::max());
   suffix=suffix.substr(0,pos);
   result = true;
   return val;

}
/*****************************************************************************\
 *
 *   Function : ssa_local_unwindert::rename
 *
 *   Input : expr - to be renamed, suffix - parent context,
 *          iteration - iteration in the current context(loop), current_loop
 *
 *   Output :
 *
 *   Purpose : expr is renamed with iteration of the current_loop appended
 *             if it is modified in the current_loop or if it starts
 *             with "$cond" or "$guard". For all other cases,
 *             only the parent context (suffix) is added to the expression
 *
 *             A negative iteration indicates that it must only get parent
 *             suffix
 *
 *
 *
 *
 *****************************************************************************/
void ssa_local_unwindert::rename(exprt &expr, std::string suffix,
    const int iteration,tree_loopnodet& current_loop) {
  if (expr.id() == ID_symbol) {
    symbol_exprt &sexpr = to_symbol_expr(expr);
    irep_idt vid=sexpr.get_identifier();
    irep_idt base_id = get_base_name(vid);
    bool isreturnvar=(as_string(vid).find(RETVAR)!=std::string::npos);
     isreturnvar= isreturnvar||(as_string(vid).find(RETVAR1)!=std::string::npos);
    int mylevel;
    if(iteration<0)
    {

    irep_idt id = id2string(vid) + suffix;
    sexpr.set_identifier(id);
    return;
    }

    std::string s = id2string(base_id);
    if(s.find("$guard")!=std::string::npos
        || s.find("$cond")!=std::string::npos
        || isreturnvar
        || (mylevel = need_renaming(current_loop,base_id))==0)
    {

      irep_idt id=id2string(vid) + suffix + "%" + i2string(iteration);
      sexpr.set_identifier(id);
      return;
    }
    if(mylevel<0) return;

    std::string fsuffix = suffix;
    std::size_t pos;
    for(unsigned int i=1;i<mylevel;i++) //TODO: clean up signed int vs. unsigned int
    {
       pos = fsuffix.find_last_of("%");
       fsuffix = fsuffix.substr(0,pos);

    }
        irep_idt id = id2string(vid) + fsuffix;
        sexpr.set_identifier(id);
        return;
  }
  else if(expr.id()==ID_nondet_symbol)
  {

        irep_idt id = expr.get_string(ID_identifier) + suffix + "%" + i2string(iteration);
        expr.set(ID_identifier,id);
        return;
  }

  for (exprt::operandst::iterator it = expr.operands().begin();
       it != expr.operands().end(); it++) {
    rename(*it, suffix,iteration,current_loop);
  }
}
void ssa_local_unwindert::rename(local_SSAt::nodet& node, std::string suffix,
    const int iteration,tree_loopnodet& current_loop) {
  for (local_SSAt::nodet::equalitiest::iterator e_it = node.equalities.begin();
       e_it != node.equalities.end(); e_it++) {
    rename(*e_it, suffix,iteration,current_loop);
  }
  for (local_SSAt::nodet::constraintst::iterator c_it =
	 node.constraints.begin(); c_it != node.constraints.end(); c_it++) {
    rename(*c_it, suffix,iteration,current_loop);
  }
  for (local_SSAt::nodet::assertionst::iterator a_it = node.assertions.begin();
       a_it != node.assertions.end(); a_it++) {
    rename(*a_it, suffix,iteration,current_loop);
  }
  for (local_SSAt::nodet::function_callst::iterator f_it =
	 node.function_calls.begin(); f_it != node.function_calls.end(); f_it++) {
    rename(*f_it, suffix,iteration,current_loop);
  }
}
/*****************************************************************************\
 * Function : ssa_local_unwindert::unwind
 *
 * Input : current_loop - a node representing a loop, suffix - a suffix
 * representing iterations of the enclosing loops, full - representing if
 * full (0..unwind_depth) or partial unwinding
 *   (current_unwinding..unwind_depth)of the current loop needs to be done,
 *   unwind_depth - new unwind_depth which must be larger than
 *   current_unwinding,
 *
 *  Output :  new_nodes - new nodes that are created during unwinding
 *
 *  Purpose : this function does a delta unwinding of loops
 *    For example if current_unwinding==1
 *
 *    uwind1=> L1_1_head
 *     uwind1=> L2_1_head
 *              L2_1_body
 *     uwind1=> L2_connector
 *     uwind1=> L1_connector
 *        and if we move to unwind_depth==2
 *
 *     uwind2=>   L1_2_head
 *                L2_2 //full
 *                L2_1
 *      uwind2=>  L2_connector
 *                L1_1_head
 *       uwind2=>   L2_2_head // partial
 *                  L2_1
 *       uwind2=>   L2_connector
 *       uwind2=>   L1_connector
 *
 *
 *   See that for L1_1 needs to be unwound partially and so is the case of
 *   loops nested inside it
 *   L1_2 on the other hand has to be unwound fully. Also, Li_connector are
 *   loop head nodes that connect the unwinding with the rest of the code.
 *   These connections needs to be broken for incremental unwinding so
 *   their equalities are transfered as constraint where new symbol
 *   new_sym => e (e is an equality)
 *   The topmost loop head also needs to change as it is the only one
 *   where phi nodes exist
 *   is introduced. To force the equality, set new_sym to true
 *
 *   Backedge from the end of every Li_1 to Li_k_head (k being the unwind_depth)
 *   is maintained via an iterator.
 *
 *   WARNING : Order of the nodes are completely arbitrary and should not
 *   be relied on at all. e.g. In the resulting SSA.nodes, a loop body
 *   may appear after loop head
 *
 *****************************************************************************/
void ssa_local_unwindert::unwind(tree_loopnodet& current_loop,
				 std::string suffix, bool full, const unsigned int unwind_depth, symbol_exprt& new_sym,
				 local_SSAt::nodest& new_nodes) {

  // a loop has to have at least one body_node, if not, it can not
  // have a nested loop either so return
  if (current_loop.body_nodes.empty())
    return;

  for (unsigned int i = 0; i < unwind_depth; i++) {
    bool tmp = i < current_unwinding ? full : true;
    for (loop_nodest::iterator it = current_loop.loop_nodes.begin();
	 it != current_loop.loop_nodes.end(); it++) {

      unwind((*it), suffix + "%" + i2string(i), tmp, unwind_depth,new_sym, new_nodes);

    }
  }

  unsigned int min_iter = full ? 0 : current_unwinding;
  for (unsigned int i = min_iter; i < unwind_depth; i++) {
    //process the loophead first
    local_SSAt::nodest::iterator it = current_loop.body_nodes.begin();
    //unwinding is done from bottom to top, so topmost unwinding
    // is special and is done after this loop
    if (i > 0) {

      local_SSAt::nodet node = *it; //copy
      node.marked = false;
      assert(node.assertions.empty()); //loophead must not have assertions!
      for (local_SSAt::nodet::equalitiest::iterator e_it =
	     node.equalities.begin(); e_it != node.equalities.end(); e_it++) {
        if (e_it->rhs().id() != ID_if) {
          if (e_it->lhs() == SSA.guard_symbol(node.location)) {
            //ASSUME : last node in body_nodes is
            // always the back-edge node
            //This back edge nodes gives us the reachability
            //guard at the end of the loop,
            //which should be used as reachability guard
            //from previous to current iteration
            rename(e_it->lhs(), suffix, i-1,current_loop);
            exprt e = SSA.guard_symbol(
	      current_loop.body_nodes.rbegin()->location);
            rename(e, suffix, i,current_loop);
            e_it->rhs() = e;

          } else {
            rename(*e_it, suffix, i-1,current_loop);
          }
          continue;
        }

        if_exprt &e = to_if_expr(e_it->rhs());
#if 0
        if(i==0)
        {							//for the first iteration, take the input
	  //coming from above
          rename(e_it->lhs(),suffix, i,current_loop);
          e_it->rhs() = e.false_case();
        }
        else
#endif
        {
          //for other iterations, take the loopback
          //value
          e_it->rhs() = current_loop.pre_post_exprs[e.true_case()];
          rename(e_it->rhs(), suffix, i,current_loop);
          rename(e_it->lhs(), suffix, i-1,current_loop);
        }
      }
      new_nodes.push_back(node);
    }
#ifdef ASSERTION_HOISTING
    assertion_hoisting(current_loop,*it,suffix,is_kinduction,
        unwind_depth,new_sym,new_nodes);
#endif

    it++;
    //now process the rest of the nodes
    for (; it != current_loop.body_nodes.end(); it++) {
      //copy the body node, rename and store in new_nodes
      local_SSAt::nodet new_node = (*it);
      new_node.marked = false;

      rename(new_node, suffix, i,current_loop);
      if(is_kinduction && !new_node.assertions.empty() &&(
	   (current_loop.is_dowhile && i>0)
	   || (!current_loop.is_dowhile && i>1)))
      { //convert all assert to assumes for k-induction
        //except the bottom most iteration

        //assertions should be converted to assume only if you are in the step case
        //of k-induction and not the base case. that means
        // you want guardls=> assume and \not guardls => assert
        // as of now this conflicts with checking spurious examples
        //so just removing the assertion if it is NOT the bottom most iteration.
        // Unless you have checked it for all unwinding less than k, this will
        // lead to unsoundness (a bug may not be found if the assertion can fail in iterations
        //other than the last

#if 1
        exprt guard_select = SSA.name(SSA.guard_symbol(),
            local_SSAt::LOOP_SELECT, current_loop.body_nodes.rbegin()->location);
        rename(guard_select,suffix,i,current_loop);


        for(local_SSAt::nodet::assertionst::iterator ait=new_node.assertions.begin();
            ait!=new_node.assertions.end();ait++)
        {
//          new_node.constraints.push_back(implies_exprt(not_exprt(guard_select),*ait));
          new_node.constraints.push_back(implies_exprt(guard_select,*ait));
//          new_node.constraints.push_back(*ait);
        }
#else
      //for linear k-induction (k increases only by 1, you do not need to check if
        //you are in the step case or not, since for k-1 even base case must have hold
        new_node.constraints.insert(new_node.constraints.end(),new_node.assertions.begin(),new_node.assertions.end());
#endif
      new_node.assertions.clear();
      }
      else if(is_ibmc &&(
               (current_loop.is_dowhile && i>0)
               || (!current_loop.is_dowhile && i>1)))
           { //convert all assert to assumes for incremental-bmc
             //except the bottom most iteration

             //when you are in base case (guard_select is false)
        //for k-1 you already have proved that there is no counter-example
        //with k-1 bound. So converting assertion to assume just helps the solver


             exprt guard_select = SSA.name(SSA.guard_symbol(),
                 local_SSAt::LOOP_SELECT, current_loop.body_nodes.begin()->location);
             rename(guard_select,suffix,i,current_loop);
             for(local_SSAt::nodet::assertionst::iterator ait=new_node.assertions.begin();
                 ait!=new_node.assertions.end();ait++)
             {
               new_node.constraints.push_back(implies_exprt(not_exprt(guard_select),*ait));
             }


           new_node.assertions.clear();
           }
      new_nodes.push_back(new_node);
    }
    if(i==0)
    {
      //this is a full unwinding, so end of the loop must be stored
      local_SSAt::nodest::iterator le_it = new_nodes.end();
      le_it--; //now points to the last element of the bottom most iteration

      //store the end of this loop, its "loophead" field will be
      //pointed to the topmost loophead node
      current_loop.loopends_map[suffix] = le_it;

      {
        //add all the loop continuation expressions for the bottom most iterations %0
        //this is requested by peter
        //TODO : later document why this is needed
        exprt loopend_guard = SSA.guard_symbol(current_loop.body_nodes.rbegin()->location);
        exprt loopend_cond = SSA.cond_symbol(current_loop.body_nodes.rbegin()->location);
        rename(loopend_guard,suffix,i,current_loop);
        rename(loopend_cond,suffix,i,current_loop);
        current_loop.loop_continuation_exprs.push_back(and_exprt(loopend_guard,loopend_cond));
      }
    }

  }

  //symbol_exprt new_sym("unwind_" + i2string(unwind_depth), bool_typet());
  //SSA.enabling_exprs.push_back(new_sym);

  //only the last element in enabling_exprs needs to be
  //set to true, all others should be set to false to enable constraint
  // wrt current unwind_depth
  {
    //copy the original loop head as the first (topmost)iteration
    local_SSAt::nodest::iterator it = current_loop.body_nodes.begin();
    local_SSAt::nodet node = *it; //copy
    for (local_SSAt::nodet::equalitiest::iterator e_it =
	   node.equalities.begin(); e_it != node.equalities.end(); e_it++) {

      if (e_it->rhs().id() == ID_if)
      {
        rename(e_it->lhs(), suffix, unwind_depth-1,current_loop);
        if_exprt &e = to_if_expr(e_it->rhs());
	rename(e.cond(),suffix, unwind_depth-1,current_loop);
	rename(e.true_case(),suffix, unwind_depth-1,current_loop);

#if 0
        //VERY DIRTY HACK, condition and true case at the topmost iteration
        // are free variables, so suffixing "0" so that it always matches
        //with the bottom most iteration. Later in the analysis these suffixes
        //are needed to be matched :-(
        rename(e.cond(),suffix + "%" + i2string(0));
        rename(e.true_case(),suffix + "%" + i2string(0));
#endif
//for false_case the value comes from above so evaluate in the parent
// context
        //if no enclosing loop then no need to rename the false_case
        if(current_loop.parent!=NULL && current_loop.parent!= &root_node)
       {

        bool result;
        std::string parent_suffix = suffix;
        unsigned int parent_iteration=get_last_iteration(parent_suffix,result);

        //if there is an enclosing loop, it must return with a valid iteration
        if(!result) assert(false);

          rename(e.false_case(),parent_suffix,parent_iteration,*current_loop.parent);

       }

      }
      else if  (SSA.guard_symbol(node.location) == e_it->lhs()) {

        rename(e_it->lhs(), suffix, unwind_depth-1,current_loop);
        rename(e_it->rhs(),suffix,-1,current_loop);

      } else {
        rename(*e_it, suffix, unwind_depth-1,current_loop);
      }
      node.enabling_expr = new_sym;
      //exprt e = implies_exprt(new_sym, *e_it);
      //node.constraints.push_back(e);
    }
    //node.equalities.clear();
    new_nodes.push_back(node);


    local_SSAt::nodest::iterator le_it = new_nodes.end();
    le_it--; //points to the topmost loophead node

    //insert the backedge
    current_loop.loopends_map[suffix]->loophead=le_it;

    //print for debugging
#if 0
    std::cout << "Loop end node------" << std::endl;
    current_loop.loopends_map[suffix]->output(std::cout,SSA.ns);
    std::cout << "Corresponding loop head node----" << std::endl;
    current_loop.loopends_map[suffix]->loophead->output(std::cout,SSA.ns);
#endif


  }
  add_connector_node(current_loop,suffix,unwind_depth,new_sym,new_nodes);

}

void ssa_local_unwindert::add_connector_node(tree_loopnodet& current_loop,
          std::string suffix,
          const unsigned int unwind_depth,symbol_exprt& new_sym,local_SSAt::nodest& new_nodes)
{
    //copy the original loop head

    local_SSAt::nodet node=current_loop.body_nodes.front();
    node.marked = false;
    node.equalities.clear();
    node.assertions.clear();
    node.constraints.clear();
    node.templates.clear();


    for(expr_break_mapt::iterator e_it=current_loop.connectors.begin();
        e_it!=current_loop.connectors.end();e_it++)
     {
      exprt e = e_it->first;
      exprt re = e;
      rename(re, suffix, 0,current_loop);
      for (unsigned int i = 1; i < unwind_depth; i++) {


        exprt cond_expr = e_it->second;
        rename(cond_expr,suffix,i,current_loop);
        exprt true_expr = e;
        rename(true_expr, suffix,i,current_loop);
        exprt false_expr = re;
        re = if_exprt(cond_expr, true_expr, false_expr);
      }
      exprt rhs = re;
      exprt lhs=e;

      rename(lhs,suffix,-1,current_loop);
      node.equalities.push_back(equal_exprt(lhs,rhs));

      node.enabling_expr = new_sym;
      //exprt ie = implies_exprt(new_sym, *e_it);
      //node.constraints.push_back(ie);

    }
    //node.equalities.clear();
    new_nodes.push_back(node);
  }


void ssa_local_unwindert::loop_continuation_conditions(
    const tree_loopnodet& current_loop, exprt::operandst& loop_cont_e) const
{
  loop_cont_e.insert(loop_cont_e.end(),
      current_loop.loop_continuation_exprs.begin(),
      current_loop.loop_continuation_exprs.end());
  for(loop_nodest::const_iterator it=current_loop.loop_nodes.begin();
      it!=current_loop.loop_nodes.end();it++)
  {
    loop_continuation_conditions(*it,loop_cont_e);
  }
}

void ssa_local_unwindert::loop_continuation_conditions(
    exprt::operandst& loop_cont_e) const
{
  loop_continuation_conditions(root_node,loop_cont_e);
}

void ssa_local_unwindert::assertion_hoisting(tree_loopnodet& current_loop,
    const local_SSAt::nodet& tmp_node,
    const std::string& suffix, const bool is_kinduction,
    const unsigned int unwind_depth,
    symbol_exprt& new_sym, local_SSAt::nodest& new_nodes)

{

  if(suffix=="" && is_kinduction)
  {
    unsigned lower_bound = current_loop.is_dowhile? 1 : 2;
    exprt assertion_hoist_e = conjunction(current_loop.assertions_after_loop);
    exprt guard_select = SSA.name(SSA.guard_symbol(),
                  local_SSAt::LOOP_SELECT, current_loop.body_nodes.rbegin()->location);
      rename(guard_select,suffix,unwind_depth-1,current_loop);
 for(unsigned int i=lower_bound;i<unwind_depth;i++)
 {
    //assertion hoisting
    //if(suffix=="" && (is_kinduction &&(
     //   (current_loop.is_dowhile && (i-1)>0)
      //  || (!current_loop.is_dowhile && (i-1)>1))))
   // {
      local_SSAt::nodet node= tmp_node;
      node.marked=false;
      node.assertions.clear();
      node.equalities.clear();
      node.constraints.clear();
      node.templates.clear();
      node.assertions_after_loop.clear();

    //  if(is_kinduction &&(
    // (current_loop.is_dowhile && (i-1)>0)
    // || (!current_loop.is_dowhile && (i-1)>1)))
     // { //convert all assert to assumes for k-induction
  //except the bottom most iteration

  //assertions should be converted to assume only if you are in the step case
  //of k-induction and not the base case. that means
  // you want guardls=> assume and \not guardls => assert
  // as of now this conflicts with checking spurious examples
  //so just removing the assertion if it is NOT the bottom most iteration.
  // Unless you have checked it for all unwinding less than k, this will
  // lead to unsoundness (a bug may not be found if the assertion can fail in iterations
  //other than the last




  //if outermost loop, do the assertion hoisting.
  //for innerloop assertion hoisting is not necessary because assertions are
  //assumed in the parent context anyway

  exprt exit_cond_e=current_loop.exit_condition;
  if(!assertion_hoist_e.is_true()&& !exit_cond_e.is_false())
  {
    //rename(assertion_hoist_e,suffix,-1,current_loop);

    rename(exit_cond_e,suffix,i,current_loop);

    exprt hoist_cond_e = and_exprt(guard_select,exit_cond_e);

    node.constraints.push_back(implies_exprt(hoist_cond_e,assertion_hoist_e));
    node.enabling_expr = new_sym;
    new_nodes.push_back(node);
  }

     // }
    }
  }

}
/*****************************************************************************\
 *
 * Function : ssa_local_unwindert::unwinder_rename
 *
 * Input : var, node
 *
 * Output : var is returned with a suffix that reflects the current unwinding
 *          with the context taken from the node
 *
 *          E.g.
 *
 *          node must look like
 *
 *          cond"somesuffix" == TRUE
 *
 *          e.g. cond%1%2%5%0 == TRUE
 *
 *          and variable might be guard#ls25
 *
 *          if the current_unwinding is 6
 *
 *          the variable should be converted to guard#ls25%1%2%5%5
 *
 *          Note that if current_unwinding is X then suffixes can have at most
 *          X-1 in its parts
 *
 *****************************************************************************/

void ssa_local_unwindert::unwinder_rename(symbol_exprt &var,
  const local_SSAt::nodet &node, bool pre) const
{
  //only to be called for backedge nodes
  //This is very dirty hack :-(
  if(current_unwinding==0) return;
  assert(node.equalities.size()>=1);
  //copy suffix from equality lhs to var
  std::string id = 
    id2string(to_symbol_expr(node.equalities[0].op0()).get_identifier());
  size_t pos = id.find_first_of("%");
  if(pos==std::string::npos) return;
  size_t pos1 = id.find_last_of("%");
  std::string suffix;
  unsigned unwinding = pre ? current_unwinding-1 : 0;
  if(pos==pos1)
  {
     suffix = "%"+i2string(unwinding);
  }
  else
  {
    suffix = id.substr(pos,pos1-pos);
    suffix += "%"+i2string(unwinding);
  }


  var.set_identifier(id2string(var.get_identifier())+suffix);
#ifdef DEBUG
  std::cout << "new id: " << var.get_identifier() << std::endl;
#endif
}


unsigned ssa_local_unwindert::rename_required(const exprt& e,
    const unsigned prev_unwinding) const
{
  if(e.id()==ID_symbol)
    {
      const symbol_exprt& sym=to_symbol_expr(e);
      irep_idt id = sym.get_identifier();

      std::list<unsigned> iterations;
      irep_idt basename;
      dissect_loop_suffix(id,basename,iterations,false);
      bool rename_required=true;
      for(std::list<unsigned>::iterator it=iterations.begin();
          it!=iterations.end();it++)
      {
        if(*it!=(prev_unwinding-1)) rename_required=false;
      }
      //if(iterations.back()==(prev_unwinding-1)) return iterations.size();
      if(rename_required) return iterations.size();


    }
    else
    {
      if(!e.operands().empty())
      {
        for(exprt::operandst::const_iterator e_it=e.operands().begin();
            e_it!=e.operands().end();e_it++)
        {
          unsigned depth=rename_required(*e_it,prev_unwinding);
          if(depth) return depth;
        }
      }
    }

      return 0;

}


void ssa_local_unwindert::rename_invariant(exprt& e,const irep_idt& suffix) const
{
  if(e.id()==ID_symbol)
  {
    symbol_exprt& sym=to_symbol_expr(e);
    irep_idt id = sym.get_identifier();

    std::list<unsigned> iterations;
    irep_idt basename;
    dissect_loop_suffix(id,basename,iterations,true);


    sym.set_identifier(id2string(basename)+id2string(suffix));
  }
  else
  {
    if(!e.operands().empty())
    {
      for(exprt::operandst::iterator e_it=e.operands().begin();
          e_it!=e.operands().end();e_it++)
      {
        rename_invariant(*e_it,suffix);
      }
    }
  }

}
/*****************************************************************************
 *
 *  Function : ssa_local_unwindert::rename_invariant
 *
 *  Input : inv_in - list of input invariants that is to be renamed for reuse
 *
 *  Output : inv_out - list of renamed invariants
 *
 *  Purpose : For the purpose of reuse of invariant, rename all
 *
 *
 *****************************************************************************/
void ssa_local_unwindert::rename_invariant(const exprt::operandst& inv_in,
    std::vector<exprt>& inv_out,const unsigned prev_unwinding) const
{

  if(prev_unwinding==0 || prev_unwinding==std::numeric_limits<unsigned int>::max())
  {
    return;
  }
  for(std::vector<exprt>::const_iterator e_it=inv_in.begin();
      e_it!=inv_in.end();e_it++)
  {
    unsigned depth=rename_required(*e_it,prev_unwinding);
    if(depth==0) continue;

    std::vector<unsigned> iter_vector(depth-1,current_unwinding-1);

    do
    {

      irep_idt suffix;

      for(std::vector<unsigned>::const_iterator vit=iter_vector.begin();
          vit!=iter_vector.end();vit++)
      {

        suffix = id2string(suffix)+"%"+i2string(*vit);
      }
      suffix = id2string(suffix)+"%"+i2string(current_unwinding-1);
      inv_out.push_back(*e_it);
      exprt& e = inv_out.back();
      rename_invariant(e,suffix);
    } while(odometer_increment(iter_vector,current_unwinding));
  }
}

exprt ssa_local_unwindert::rename_invariant(const exprt& inv_in) const
{
  if(inv_in.is_true()) return inv_in;

  exprt::operandst inv_in_operands; 
  if(inv_in.id()!=ID_and) inv_in_operands.push_back(inv_in);
  else inv_in_operands = inv_in.operands();

 std::vector<exprt> new_inv;
 rename_invariant(inv_in_operands,new_inv,prev_unwinding);

 return conjunction(new_inv);
}


bool ssa_local_unwindert::odometer_increment(std::vector<unsigned>& odometer,
    unsigned base) const
{
  if(odometer.empty()) return false;
  unsigned i=odometer.size()-1;
  while(true)
  {
    if(odometer[i] < base-1) {odometer[i]++; return true;}
    odometer[i]=0;
    if(i==0) return false; //overflow
    i--;

  }
return false;
}
/*****************************************************************************\
 *
 * Function : ssa_unwindert::ssa_unwindert
 *
 * Input : reference to ssa_db
 *
 * Output :
 *
 * Purpose : Constructor, set is_initialized to false. Initializer init()
 * must be invoked before unwind functions are called
 *
 *****************************************************************************/
ssa_unwindert::ssa_unwindert(ssa_dbt& _db) :
  ssa_db(_db),is_initialized(false) {


}

/*****************************************************************************\
 *
 * Function : ssa_new_unwindert::unwind
 *
 * Input : id - name of the goto-function to be unwound, k - unwinding depth
 *
 * Output : false - if id does not correspond to any goto-function in the
 * 			unwinder_map
 *
 * Purpose : incrementally unwind a function 'id' up to depth k. Initializer
 * must have been invoked before calling this function
 *
 *****************************************************************************/

void ssa_unwindert::unwind(const irep_idt id, unsigned int k) {
  assert(is_initialized);
  unwinder_mapt::iterator it;

  it = unwinder_map.find(id);
  if (it == unwinder_map.end())
    assert(false && "Function not found");
  it->second.unwind(it->first,k);

}

/*****************************************************************************\
 *
 * Function :
 *
 * Input :
 *
 * Output :
 *
 * Purpose :
 *
 *****************************************************************************/

void ssa_unwindert::unwind_all(unsigned int k) {

  assert(is_initialized);

  for (unwinder_mapt::iterator it = unwinder_map.begin();
       it != unwinder_map.end(); it++) {
    it->second.unwind(it->first,k);
  }

}

/*****************************************************************************\
 *
 * Function :
 *
 * Input :
 *
 * Output :
 *
 * Purpose :
 *
 *****************************************************************************/

void ssa_unwindert::output(std::ostream & out) {
  if(!is_initialized) return;
  for (unwinder_mapt::iterator it = unwinder_map.begin();
       it != unwinder_map.end(); it++) {
    out << "Unwinding for function" << it->first << std::endl;
    it->second.output(out);
  }
}

/*****************************************************************************\
 *
 * Function : ssa_unwindert::init
 *
 * Input :
 *
 * Output :
 *
 * Purpose : Initialize unwinder_map by computing hierarchical tree_loopnodet
 *           for every goto-function
 *           Set is_initialized to true. Initializer must be called before
 *           unwind funcitions are called.
 *
 *****************************************************************************/
void ssa_unwindert::init(bool kinduction, bool _ibmc)
{
  ssa_dbt::functionst& funcs = ssa_db.functions();
  for (ssa_dbt::functionst::iterator it = funcs.begin(); it != funcs.end();
       it++) {
    unwinder_map.insert(
      unwinder_pairt(it->first, ssa_local_unwindert((*(it->second)),kinduction,_ibmc)));
  }


}

void ssa_unwindert::init_localunwinders()
{
  for(unwinder_mapt::iterator it=unwinder_map.begin();
      it!=unwinder_map.end();it++)
  {
     it->second.set_return_var(it->first);
     it->second.init();
  }
  is_initialized=true;
}
