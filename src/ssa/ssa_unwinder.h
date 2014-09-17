/*******************************************************************\

Module: SSA Unwinder

Author: Peter Schrammel

\*******************************************************************/

#ifndef CPROVER_DELTACHECK_SSA_UNWINDER_H
#define CPROVER_DELTACHECK_SSA_UNWINDER_H

#include <util/message.h>

#include "../ssa/local_ssa.h"
#include "../summarizer/ssa_db.h"

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

class ssa_local_unwindert	: public messaget
{
	local_SSAt& SSA;
	unsigned int current_unwinding;
	class tree_loopnodet;
	typedef std::list<tree_loopnodet> loop_nodest;
	bool loopless;
	class tree_loopnodet
	{
	public:
		local_SSAt::nodest body_nodes;
		//local_SSAt::nodet::iterator loophead_node;
		std::map<exprt,exprt> pre_post_exprs;
#if 0
		symbol_exprt entry_guard;
		symbol_exprt exit_guard;
		symbol_exprt cond_expr;
#endif
		loop_nodest loop_nodes;

		tree_loopnodet(){}

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
	void construct_loop_tree();
	void unwind(tree_loopnodet& current_loop,
			std::string suffix,bool full,
			const unsigned int unwind_depth,local_SSAt::nodest& new_ndoes);
	void rename(local_SSAt::nodet& node,std::string suffix);
	void rename(exprt &expr, std::string suffix);

public :
	void output(std::ostream& out)
	{
		//root_node.output(out,SSA.ns);
		SSA.output(out);
	}
	std::list<symbol_exprt> enabling_exprs;
	ssa_local_unwindert(local_SSAt& _SSA): SSA(_SSA),
			current_unwinding(0){ construct_loop_tree();}
	bool unwind(unsigned int k);

};

class ssa_new_unwindert	: public messaget
{

public:
	typedef std::map<irep_idt,ssa_local_unwindert> unwinder_mapt;
		typedef std::pair<irep_idt,ssa_local_unwindert> unwinder_pairt;
	ssa_new_unwindert(ssa_dbt& _db);

	bool unwind(const irep_idt id,unsigned int k);

	bool unwind_all(unsigned int k);

	void output(std::ostream & out);
protected:
	ssa_dbt& ssa_db;

	unwinder_mapt unwinder_map;

};

#endif
