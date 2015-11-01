/*******************************************************************\

Module: SSA Unwinder

Author: Saurabh Joshi

\*******************************************************************/

#ifndef CPROVER_DELTACHECK_SSA_UNWINDER_H
#define CPROVER_DELTACHECK_SSA_UNWINDER_H

#include <util/message.h>

#include "../ssa/local_ssa.h"
#include "../summarizer/ssa_db.h"

#define RETVAR "#return_value"
#define RETVAR1 "return_value___VERIFIER_nondet"

struct compare_node_iteratorst {
  bool operator()(const local_SSAt::nodest::iterator& a,
      const local_SSAt::nodest::iterator& b) const;
  bool operator()(const local_SSAt::nodest::const_iterator& a,
      const local_SSAt::nodest::const_iterator& b) const;
};

class ssa_local_unwindert : public messaget
{
  irep_idt return_var;
  bool isvoid;
  local_SSAt& SSA;
  unsigned int current_unwinding;
  unsigned int prev_unwinding;
  class tree_loopnodet;
  typedef std::list<tree_loopnodet> loop_nodest;
  typedef std::map<irep_idt,local_SSAt::nodest::iterator> loopends_mapt;
  typedef std::map<irep_idt,int> modvar_levelt;
  typedef std::set<exprt> exprst;
  typedef exprt cond_et;
  typedef exprt guard_et;
  typedef std::map<exprt, exprt> expr_break_mapt;
  typedef std::pair<exprt,exprt> exp_guard_cond_pairt;
  typedef std::set<local_SSAt::nodest::const_iterator,compare_node_iteratorst> return_nodest;
  typedef local_SSAt::nodest body_nodest;
  bool loopless;

  class tree_loopnodet
  {
  public:
    return_nodest return_nodes;
    //exprst connectors;
    exprt::operandst assertions_after_loop;
    exprt::operandst loop_continuation_exprs;
    exprt exit_condition;
    expr_break_mapt connectors;
    tree_loopnodet* parent;
    local_SSAt::nodest body_nodes;
    std::map<exprt,exprt> pre_post_exprs;
    modvar_levelt modvar_level;
    std::set<irep_idt> vars_modified;
#if 0
    symbol_exprt entry_guard;
    symbol_exprt exit_guard;
    symbol_exprt cond_expr;
#endif
    loop_nodest loop_nodes;
    loopends_mapt loopends_map;
    bool is_dowhile;

    tree_loopnodet(){parent=NULL;is_dowhile=false;}

    void output(std::ostream& out,const namespacet& ns)
    {


      out << "Body nodes" << std::endl;
      for(local_SSAt::nodest::iterator it=body_nodes.begin();
	  it!=body_nodes.end();it++)
      {
	it->output(out,ns);
      }
      out << "Nested loop nodes" << std::endl;
      for(loop_nodest::iterator it=loop_nodes.begin();
	  it!=loop_nodes.end();it++)
      {
	it->output(out,ns);

      }

    }
  };
  tree_loopnodet root_node;
  std::string keep_first_two_hash(const std::string& str) const;
  void put_varmod_in_parent();
  void populate_parents();
  void propagate_varmod_to_ancestors(const irep_idt& id,
      tree_loopnodet* current_loop);
  void populate_return_val_mod();
  void is_void_func();
  bool is_break_node(const local_SSAt::nodet& node,
      const unsigned int end_location) const;
  bool is_return_node(const tree_loopnodet& current_loop,
      const local_SSAt::nodest::const_iterator& node) const;

  void populate_connectors(tree_loopnodet& current_loop);
  void unwind(tree_loopnodet& current_loop,
	      std::string suffix,bool full,
	      const unsigned int unwind_depth,symbol_exprt& new_sym,
	      local_SSAt::nodest& new_nodes);
  void rename(local_SSAt::nodet& node,std::string suffix,
      const int iteration,tree_loopnodet& current_loop);
  void rename(exprt &expr, std::string suffix,
      const int iteration,tree_loopnodet& current_loop);
  int need_renaming(tree_loopnodet& current_loop,
      const irep_idt& id);
  unsigned int get_last_iteration(std::string& suffix, bool& result);
  irep_idt get_base_name(const irep_idt& id);
  unsigned rename_required(const exprt& e,
      const unsigned prev_unwinding) const;
  void rename_invariant(exprt& e,const irep_idt& suffix) const;
  void add_connector_node(tree_loopnodet& current_loop,
          std::string suffix,
          const unsigned int unwind_depth,
          symbol_exprt& new_sym,
          local_SSAt::nodest& new_nodes);
  void loop_continuation_conditions(
      const tree_loopnodet& current_loop, exprt::operandst& loop_cont_e) const;
  void assertion_hoisting(tree_loopnodet& current_loop,
      const local_SSAt::nodet& tmp_node,
      const std::string& suffix, const bool is_kinduction,
      const unsigned int unwind_depth,
      symbol_exprt& new_sym, local_SSAt::nodest& new_nodes);
  bool is_initialized;
public :
  void set_return_var(const irep_idt& id);
  void dissect_loop_suffix(const irep_idt& id,
      irep_idt& before_suffix,
      std::list<unsigned>& iterations, bool baseonly) const;
  void rename_invariant(const std::vector<exprt>& inv_in,
      std::vector<exprt>& inv_out,const unsigned prev_unwinding) const;
  exprt rename_invariant(const exprt& inv_in) const;
  void loop_continuation_conditions(exprt::operandst& loop_cont_e) const;
  bool odometer_increment(std::vector<unsigned>& odometer,
      unsigned base) const;
  bool is_kinduction;
  bool is_ibmc;
  void init();
  void output(std::ostream& out)
  {
    SSA.output(out);
  }
ssa_local_unwindert(local_SSAt& _SSA, bool k_induct, bool _ibmc);
  void unwind(const irep_idt& fname,unsigned int k);

  void unwinder_rename(symbol_exprt &var,const local_SSAt::nodet &node, bool pre) const;
};

class ssa_unwindert	: public messaget
{

public:
  typedef std::map<irep_idt,ssa_local_unwindert> unwinder_mapt;
  typedef std::pair<irep_idt,ssa_local_unwindert> unwinder_pairt;

  ssa_unwindert(ssa_dbt& _db);

  void init(bool kinduction, bool _ibmc);

  void init_localunwinders();

  void unwind(const irep_idt id,unsigned int k);

  void unwind_all(unsigned int k);

  ssa_local_unwindert &get(const irep_idt& fname) { return unwinder_map.at(fname); }

  void output(std::ostream & out);

protected:
  ssa_dbt& ssa_db;
  bool is_initialized;
  unwinder_mapt unwinder_map;

};

#endif
