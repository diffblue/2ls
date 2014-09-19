/*******************************************************************
 Module: SSA Unwinder

 Author: Peter Schrammel

 \*******************************************************************/

#include <iostream>

#include <util/i2string.h>

#include "ssa_unwinder.h"

/*******************************************************************
 Function: ssa_unwindert::unwind

 Inputs:

 Outputs: 

 Purpose: unwinds all loops the given number of times

 \*******************************************************************/

#if 0
void ssa_unwindert::unwind(local_SSAt &SSA, unsigned unwind_max) {
  if (unwind_max == 0)
    return;

  for (local_SSAt::nodest::iterator n_it = SSA.nodes.begin();
       n_it != SSA.nodes.end(); n_it++) {
    if (n_it->loophead == SSA.nodes.end())
      continue;
    //we've found a loop

    local_SSAt::locationt loop_head = n_it->loophead->location;

    std::cout << "loop head: " << std::endl;
    n_it->loophead->output(std::cout, SSA.ns);

    // get variables at beginning and end of loop body
    std::map<exprt, exprt> pre_post_exprs;

    const ssa_domaint::phi_nodest &phi_nodes =
      SSA.ssa_analysis[loop_head].phi_nodes;

    for (local_SSAt::objectst::const_iterator o_it =
	   SSA.ssa_objects.objects.begin(); o_it != SSA.ssa_objects.objects.end();
	 o_it++) {
      ssa_domaint::phi_nodest::const_iterator p_it = phi_nodes.find(
	o_it->get_identifier());

      if (p_it == phi_nodes.end())
        continue; // object not modified in this loop

      symbol_exprt pre = SSA.name(*o_it, local_SSAt::LOOP_BACK, n_it->location);
      symbol_exprt post = SSA.read_rhs(*o_it, n_it->location);

      pre_post_exprs[pre] = post;
    }

    // unwind that loop
    for (unsigned unwind = unwind_max; unwind > 0; unwind--) {
      // insert loop_head
      local_SSAt::nodet node = *n_it->loophead; //copy
      for (local_SSAt::nodet::equalitiest::iterator e_it =
	     node.equalities.begin(); e_it != node.equalities.end(); e_it++) {
        if (e_it->rhs().id() != ID_if) {
          rename(*e_it, unwind);
          continue;
        }

        if_exprt &e = to_if_expr(e_it->rhs());

        if (unwind == unwind_max) {
          rename(e_it->lhs(), unwind);
          e_it->rhs() = e.false_case();
        } else {
          e_it->rhs() = pre_post_exprs[e.true_case()];
          rename(e_it->rhs(), unwind + 1);
          rename(e_it->lhs(), unwind);
        }
      }
      new_nodes.push_back(node);

      // insert body
      local_SSAt::nodest::iterator it = n_it->loophead;
      it++;
      for (; it != n_it; it++) {
        local_SSAt::nodet n = *it; //copy;
        rename(n, unwind);
        new_nodes.push_back(n);
      }
    }

    // feed last unwinding into original loop_head, modified in place
    for (local_SSAt::nodet::equalitiest::iterator e_it =
	   n_it->loophead->equalities.begin();
	 e_it != n_it->loophead->equalities.end(); e_it++) {
      if (e_it->rhs().id() != ID_if)
        continue;

      if_exprt &e = to_if_expr(e_it->rhs());
      e.false_case() = pre_post_exprs[e.true_case()];
      rename(e.false_case(), 1);
    }
    commit_nodes(SSA.nodes, n_it->loophead); //apply changes

#if 0
    std::cout << "SSA after loop: " << std::endl;
    SSA.output(std::cout);
#endif
  }
}

/*******************************************************************
 Function: ssa_unwindert::rename()

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

void ssa_unwindert::rename(exprt &expr, unsigned index) {
  if (expr.id() == ID_symbol) {
    symbol_exprt &sexpr = to_symbol_expr(expr);
    irep_idt id = id2string(sexpr.get_identifier()) + "%" + i2string(index);
    sexpr.set_identifier(id);
  }
  for (exprt::operandst::iterator it = expr.operands().begin();
       it != expr.operands().end(); it++) {
    rename(*it, index);
  }
}

/*******************************************************************
 Function: ssa_inlinert::rename()

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

void ssa_unwindert::rename(local_SSAt::nodet &node, unsigned index) {
  for (local_SSAt::nodet::equalitiest::iterator e_it = node.equalities.begin();
       e_it != node.equalities.end(); e_it++) {
    rename(*e_it, index);
  }
  for (local_SSAt::nodet::constraintst::iterator c_it =
	 node.constraints.begin(); c_it != node.constraints.end(); c_it++) {
    rename(*c_it, index);
  }
  for (local_SSAt::nodet::assertionst::iterator a_it = node.assertions.begin();
       a_it != node.assertions.end(); a_it++) {
    rename(*a_it, index);
  }
  for (local_SSAt::nodet::function_callst::iterator f_it =
	 node.function_calls.begin(); f_it != node.function_calls.end(); f_it++) {
    rename(*f_it, index);
  }
}

/*******************************************************************
 Function: ssa_unwindert::commit_nodes()

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

void ssa_unwindert::commit_nodes(local_SSAt::nodest &nodes,
				 local_SSAt::nodest::iterator n_pos) {
  nodes.splice(n_pos, new_nodes, new_nodes.begin(), new_nodes.end());
}

#else
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
ssa_local_unwindert::ssa_local_unwindert(local_SSAt& _SSA): SSA(_SSA),
    current_unwinding(0),is_initialized(false){ }
/*******************************************************************
 Struct: compare_node_iterators

 Inputs:

 Outputs:

 Purpose: a function object to pass as a comparator for std::set
 to enable us to order iterators. It takes the address of the
 object being pointed to by iterators and compared them as
 unsigned long

 \*******************************************************************/
struct compare_node_iteratorst {
  bool operator()(const local_SSAt::nodest::iterator& a,
		  const local_SSAt::nodest::iterator& b) const {
    return ((unsigned long) (&(*a)) < (unsigned long) (&(*b)));
  }
};
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
      current_node->body_nodes.push_back(*n_it);

      //reset the back-edge
      current_node->body_nodes.rbegin()->loophead=SSA.nodes.end();

      {
        local_SSAt::nodet loophead = current_node->body_nodes.front();
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
      //hope push_back does a copy by value
      new_current_node->loop_nodes.push_back(*current_node);

      delete current_node;

      current_node = new_current_node;
    } else {
      //a normal node belongs to body_nodes of the current loop
      current_node->body_nodes.push_back(*n_it);
    }

  }
  //only the top level body_nodes are required
  // all other required nodes will be inserted during unwinding
  // so avoid duplicates by removing them from SSA.nodes
  SSA.nodes.clear();
  SSA.nodes.insert(SSA.nodes.begin(), root_node.body_nodes.begin(),
		   root_node.body_nodes.end());
  is_initialized=true;

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
  local_SSAt::nodest new_nodes;
  irep_idt func_name = as_string(fname)+"unwind_"+i2string(k);
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
void ssa_local_unwindert::rename(exprt &expr, std::string suffix) {
  if (expr.id() == ID_symbol) {
    symbol_exprt &sexpr = to_symbol_expr(expr);
    irep_idt id = id2string(sexpr.get_identifier()) + suffix;
    sexpr.set_identifier(id);
  }
  for (exprt::operandst::iterator it = expr.operands().begin();
       it != expr.operands().end(); it++) {
    rename(*it, suffix);
  }
}
void ssa_local_unwindert::rename(local_SSAt::nodet& node, std::string suffix) {
  for (local_SSAt::nodet::equalitiest::iterator e_it = node.equalities.begin();
       e_it != node.equalities.end(); e_it++) {
    rename(*e_it, suffix);
  }
  for (local_SSAt::nodet::constraintst::iterator c_it =
	 node.constraints.begin(); c_it != node.constraints.end(); c_it++) {
    rename(*c_it, suffix);
  }
  for (local_SSAt::nodet::assertionst::iterator a_it = node.assertions.begin();
       a_it != node.assertions.end(); a_it++) {
    rename(*a_it, suffix);
  }
  for (local_SSAt::nodet::function_callst::iterator f_it =
	 node.function_calls.begin(); f_it != node.function_calls.end(); f_it++) {
    rename(*f_it, suffix);
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
            rename(e_it->lhs(), suffix + '%' + i2string(i - 1));
            exprt e = SSA.guard_symbol(
	      current_loop.body_nodes.rbegin()->location);
            rename(e, suffix + "%" + i2string(i));
            e_it->rhs() = e;

          } else {
            rename(*e_it, suffix + "%" + i2string(i - 1));
          }
          continue;
        }

        if_exprt &e = to_if_expr(e_it->rhs());
#if 0
        if(i==0)
        {							//for the first iteration, take the input
	  //coming from above
          rename(e_it->lhs(),suffix+"%"+i2string(i));
          e_it->rhs() = e.false_case();
        }
        else
#endif
        {
          //for other iterations, take the loopback
          //value
          e_it->rhs() = current_loop.pre_post_exprs[e.true_case()];
          rename(e_it->rhs(), suffix + "%" + i2string(i));
          rename(e_it->lhs(), suffix + "%" + i2string(i - 1));
        }
      }
      new_nodes.push_back(node);
    }

    it++;
    //now process the rest of the nodes
    for (; it != current_loop.body_nodes.end(); it++) {
      //copy the body node, rename and store in new_nodes
      local_SSAt::nodet new_node = (*it);

      rename(new_node, suffix + "%" + i2string(i));
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
        rename(e_it->lhs(), suffix + "%" + i2string(unwind_depth - 1));
        if_exprt &e = to_if_expr(e_it->rhs());
	rename(e.cond(),suffix + "%" + i2string(unwind_depth - 1));
	rename(e.true_case(),suffix + "%" + i2string(unwind_depth - 1));

#if 0
        //VERY DIRTY HACK, condition and true case at the topmost iteration
        // are free variables, so suffixing "0" so that it always matches
        //with the bottom most iteration. Later in the analysis these suffixes
        //are needed to be matched :-(
        rename(e.cond(),suffix + "%" + i2string(0));
        rename(e.true_case(),suffix + "%" + i2string(0));
#endif
        rename(e.false_case(),suffix);
      }
      else if  (SSA.guard_symbol(node.location) == e_it->lhs()) {

        rename(e_it->lhs(), suffix + "%" + i2string(unwind_depth - 1));
        rename(e_it->rhs(),suffix);

      } else {
        rename(*e_it, suffix + "%" + i2string(unwind_depth - 1));
      }
      exprt e = implies_exprt(new_sym, *e_it);
      node.constraints.push_back(e);
    }
    node.equalities.clear();
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

  //now the connector node
  {
    //copy the original loop head

    local_SSAt::nodet node = current_loop.body_nodes.front();

    exprt guard_e = SSA.guard_symbol(node.location);
    exprt cond_e = SSA.cond_symbol(node.location);
    for (local_SSAt::nodet::equalitiest::iterator e_it =
	   node.equalities.begin(); e_it != node.equalities.end(); e_it++) {
      exprt e = e_it->lhs();
      exprt re = e;
      rename(re, suffix + "%" + i2string(0));
      for (unsigned int i = 1; i < unwind_depth; i++) {
        exprt ce = cond_e;
        rename(ce, suffix + "%" + i2string(i));
        exprt ge = guard_e;
        rename(ge, suffix + "%" + i2string(i));

        exprt cond_expr = and_exprt(ce, ge);
        exprt true_expr = e;
        rename(true_expr, suffix + "%" + i2string(i));
        exprt false_expr = re;
        re = if_exprt(cond_expr, true_expr, false_expr);
      }

      e_it->rhs() = re;
      rename(e_it->lhs(),suffix);

      exprt ie = implies_exprt(new_sym, *e_it);
      node.constraints.push_back(ie);

    }
    node.equalities.clear();
    new_nodes.push_back(node);
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
  //The node _MUST_ look like cond"suffix" = TRUE
  //This is very dirty hack :-(
  assert(node.equalities.size()==1);
  if(current_unwinding==0) return;
  //this is a hack: copy suffix from 'cond' equality to var
  std::string id = id2string(to_symbol_expr(node.equalities[0].op0()).get_identifier());
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
void ssa_unwindert::init()
{
  ssa_dbt::functionst& funcs = ssa_db.functions();
  for (ssa_dbt::functionst::iterator it = funcs.begin(); it != funcs.end();
       it++) {
    unwinder_map.insert(
      unwinder_pairt(it->first, ssa_local_unwindert((*(it->second)))));
  }


}

void ssa_unwindert::init_localunwinders()
{
  for(unwinder_mapt::iterator it=unwinder_map.begin();
      it!=unwinder_map.end();it++)
  {
     it->second.init();
  }
  is_initialized=true;
}

#endif
