/*******************************************************************\

Module: SSA Unwinder

Author: Peter Schrammel

\*******************************************************************/

#ifndef CPROVER_DELTACHECK_SSA_UNWINDER_H
#define CPROVER_DELTACHECK_SSA_UNWINDER_H

#include <util/message.h>

#include "../ssa/local_ssa.h"
#include "../summarizer/ssa_db.h"
#if 0
class ssa_unwindert : public messaget
{
 public:
  ssa_unwindert() {}

  void unwind(local_SSAt &SSA, unsigned unwind);

 protected:
  void commit_nodes(local_SSAt::nodest &nodes,
                    local_SSAt::nodest::iterator n_pos);
  local_SSAt::nodest new_nodes;

  void rename(exprt &expr, unsigned index);
  void rename(local_SSAt::nodet &node, unsigned index);

};
#else

class ssa_local_unwindert : public messaget
{
  local_SSAt& SSA;
  unsigned int current_unwinding;
  class tree_loopnodet;
  typedef std::list<tree_loopnodet> loop_nodest;
  typedef std::map<irep_idt,local_SSAt::nodest::iterator> loopends_mapt;
  typedef std::map<irep_idt,int> modvar_levelt;
  typedef std::set<exprt> exprst;
  typedef local_SSAt::nodest body_nodest;
  bool loopless;
  class tree_loopnodet
  {
  public:
    exprst connectors;
    tree_loopnodet* parent;
    local_SSAt::nodest body_nodes;
    //local_SSAt::nodet::iterator loophead_node;
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
  bool is_break_node(const local_SSAt::nodet& node,const unsigned int end_location);
  void populate_connectors(tree_loopnodet& current_loop);
  void unwind(tree_loopnodet& current_loop,
	      std::string suffix,bool full,
	      const unsigned int unwind_depth,symbol_exprt& new_sym,local_SSAt::nodest& new_nodes);
  void rename(local_SSAt::nodet& node,std::string suffix,
      const int iteration,tree_loopnodet& current_loop);
  void rename(exprt &expr, std::string suffix,
      const int iteration,tree_loopnodet& current_loop);
  int need_renaming(tree_loopnodet& current_loop,
      const irep_idt& id);
  unsigned int get_last_iteration(std::string& suffix, bool& result);
  irep_idt get_base_name(const irep_idt& id);

  void add_connector_node(tree_loopnodet& current_loop,
          std::string suffix,
          const unsigned int unwind_depth,symbol_exprt& new_sym,local_SSAt::nodest& new_nodes);
 // void init();
  bool is_initialized;
public :
  bool is_kinduction;
  void init();
  void output(std::ostream& out)
  {
    //root_node.output(out,SSA.ns);
    SSA.output(out);
  }
  //std::list<symbol_exprt> enabling_exprs;
ssa_local_unwindert(local_SSAt& _SSA, bool k_induct);
  void unwind(const irep_idt& fname,unsigned int k);

  void unwinder_rename(symbol_exprt &var,const local_SSAt::nodet &node, bool pre) const;
};

class ssa_unwindert	: public messaget
{

public:
  typedef std::map<irep_idt,ssa_local_unwindert> unwinder_mapt;
  typedef std::pair<irep_idt,ssa_local_unwindert> unwinder_pairt;

  ssa_unwindert(ssa_dbt& _db);

  void init(bool kinduction);

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

#endif
