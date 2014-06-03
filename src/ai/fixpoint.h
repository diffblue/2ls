#ifndef CPROVER_FIXPOINT_H
#define CPROVER_FIXPOINT_H

/******************************************************************************\
Fixed point iteration for abstract interpretation 
\******************************************************************************/

#include <climits>
#include <list>
#include <map>
#include <set>
#include <vector>
#include <iostream>

#define DEBUG 1

/******************************************************************************\
CFG interface 
\******************************************************************************/
template<class Node, class Edge, class ConcreteTransformer> 
class cfgt
{
 public:
  typedef std::set<Node> nodest;
  typedef std::set<Edge> edgest;

  virtual nodest &get_nodes() = 0;
  virtual edgest &get_succ_edges(Node n) = 0;
  virtual Node get_pred_node(const Edge &e) = 0;
  virtual Node get_succ_node(const Edge &e) = 0;
  virtual const ConcreteTransformer &get_transformer(const Edge &e) = 0;
};

/******************************************************************************\
abstract domain interface 
\******************************************************************************/
template<class AbstractValue, class ConcreteTransformer> 
class domaint
{
 public:
  virtual AbstractValue bottom() = 0;
  // return true if v1 has changed
  virtual bool join(AbstractValue &v1, 
                    const AbstractValue &v2) = 0;
  // return true if v2 contains v1
  virtual bool widen(AbstractValue &v1, 
                     const AbstractValue &v2) = 0;
  virtual AbstractValue transform(const AbstractValue &v,
                                  const ConcreteTransformer &t) = 0;
                                  
  virtual void output(const AbstractValue &v, std::ostream& out)=0;
};

/******************************************************************************\
fixed point iteration class 
\******************************************************************************/
template<class Node, class Edge, class AbstractValue, class ConcreteTransformer>
class fixpointt
{
 public:
  fixpointt(cfgt<Node,Edge,ConcreteTransformer> &_cfg, 
            domaint<AbstractValue,ConcreteTransformer> &_domain) 
    : cfg(_cfg), domain(_domain) {}

  typedef typename cfgt<Node,Edge,ConcreteTransformer>::nodest nodest;
  typedef typename cfgt<Node,Edge,ConcreteTransformer>::edgest edgest;
  typedef std::map<Node,AbstractValue> resultt;

  typedef hash_set_cont<Node> visitedt;

  /****************************************************************************/
  void analyze(const Node initial_node,
               const AbstractValue &initial_value, 
               unsigned widening_start,
               unsigned widening_descend,
               resultt &result)
  {
    //compute iteration strategy
    strategyt strategy = compute_strategy(initial_node);

    //initialize result structure
    nodest &nodes = cfg.get_nodes();
    for(typename nodest::iterator it = nodes.begin(); it!=nodes.end(); it++)
    {
      result[*it] = domain.bottom();
    }
    result[initial_node] = initial_value;

    //run strategy
    run_strategy(strategy,result,widening_start,widening_descend);
  }


  void output(std::ostream &out, resultt &result)
  {
    out << "fixpointt output\n";
  
    for(typename resultt::const_iterator
        map_it=result.begin();
        map_it!=result.end();
        ++map_it)
    {
      out << map_it->first << " ";
      domain.output(map_it->second, out);
      out << "\n";
    }
  }


 protected:
  cfgt<Node,Edge,ConcreteTransformer> &cfg;
  domaint<AbstractValue,ConcreteTransformer> &domain;

  class strategy_nodet
  {
   public:
    Node node;
    bool do_widen;
    unsigned loop_head_index;
  }; 

  typedef std::vector<strategy_nodet> strategyt;

  /****************************************************************************/
  strategyt compute_strategy(const Node initial_node)
  {
    //compute weak topological ordering, flattens all loops below top-level
    std::map<unsigned, std::set<Node> > scc_map;
    //Tarjan SCC
    unsigned index = 0;
    visitedt visited;
    std::list<Node> stack;
    std::map<Node , unsigned> indices;
    std::map<Node , unsigned> lowlinks;
    scc_rec(initial_node,scc_map,visited,stack,index,indices,lowlinks);

    //create strategy structure
    strategyt strategy;
    strategy.resize(visited.size());

    index = 0;
    unsigned i=0;
    assert(visited.size()>0);    
    unsigned first_index_scc = UINT_MAX;
    for(typename visitedt::iterator it = visited.begin(); 
        it != visited.end(); it++, i++) 
    {
      strategy[i].node = *it;
      strategy[i].loop_head_index = UINT_MAX;
      strategy[i].do_widen = false;
      if(scc_map[index].find(*it)!=scc_map[index].end())
      {
        if(first_index_scc == UINT_MAX) // first element of scc
        {
	        first_index_scc = i;
          strategy[i].do_widen = true;
	      }
        scc_map[index].erase(*it);
        if(scc_map[index].size()==0) // last element of scc
      	{
          index++;
          strategy[i].loop_head_index = first_index_scc;
          first_index_scc = UINT_MAX;
	      }
      }
    }

#if DEBUG
    std::cout << "strategy: ";
    for(unsigned i=0;i<strategy.size();i++)
    {
      std::cout << "(" << strategy[i].node;
      if(strategy[i].do_widen) std::cout << "w";
      if(strategy[i].loop_head_index!=UINT_MAX) 
        std::cout << "l[" << strategy[i].loop_head_index << "]";
      std::cout << ")";
    }
    std::cout << std::endl;
#endif

    return strategy;
  }
  /****************************************************************************/

 private:
  /****************************************************************************/
  void scc_rec(Node n, 
               std::map<unsigned, std::set<Node> > &scc_map,
               visitedt &visited, 
	       std::list<Node> &stack, 
	       unsigned &index,
	       std::map<Node, unsigned> &indices,
	       std::map<Node, unsigned> &lowlinks)
  {
    visited.insert(n);
    stack.push_back(n);
    index++;
    indices[n] = lowlinks[n] = index;
    edgest &edges=cfg.get_succ_edges(n);
    
    for(typename edgest::iterator it = edges.begin(); 
        it != edges.end(); ++it) 
    {
      Node succ=it->succ;
    
      if(visited.find(succ)==visited.end()) 
      {
	      scc_rec(succ,scc_map,visited,stack,index,indices,lowlinks);
	      lowlinks[n] = std::min(lowlinks[succ],lowlinks[n]);
      }
      else 
      {
	      bool found = false;
	      for(typename std::list<Node>::iterator i = stack.begin(); 
	          i!=stack.end(); i++) 
        {
	        if(*i==succ) { found = true; break; }
	      }
	      
	      if(found) 
        {
	        lowlinks[n] = std::min(indices[succ],lowlinks[n]);
	      }
      }
    }
    if(lowlinks[n]!=indices[n]) return;
    Node t = stack.back();
    do 
    {
      t = stack.back();
      scc_map[lowlinks[n]].insert(t);
      stack.pop_back();
    }
    while(t!=n);
  }

  typedef hash_map_cont<Node, edgest > edges_to_processt;

  /****************************************************************************/
  void run_strategy(const strategyt &strategy, resultt &result, 
                    unsigned widening_start, unsigned widening_descend) 
  {

    edges_to_processt edges_to_process;

    for(unsigned i=0; i<strategy.size(); i++)
    {
      if(!strategy[i].do_widen) // not in a loop
      {
        process_strategy_node(strategy[i].node,result,false,edges_to_process);
      }
      else // a loop!
      {
        unsigned first_index_scc = i;
	//phase 1: ascending iterations  
#if DEBUG
        std::cout << "ascending iterations for loop at node " 
          << strategy[i].node << std::endl;
#endif
	if(!run_strategy_loop(strategy,i,
			      result,edges_to_process,widening_start,false))
	{
	  //phase 2: ascending iterations with widening
#if DEBUG
           std::cout << "ascending iterations with widening for loop at node " 
             << strategy[i].node << std::endl;
#endif
          i = first_index_scc;
	  assert(run_strategy_loop(strategy,i,
				   result,edges_to_process,UINT_MAX,true));

   	  //phase 3: descending iterations
#if DEBUG
           std::cout << "descending iterations for loop at node " 
             << strategy[i].node << std::endl;
#endif
          i = first_index_scc;
	  run_strategy_loop(strategy,i,
			    result,edges_to_process,widening_descend,false);
	}
        // i is now first index after scc
      }
    }
  }

  bool run_strategy_loop(const strategyt &strategy, unsigned &index,
		    resultt &result, edges_to_processt &edges_to_process,
                    unsigned max_iterations, bool widen) 
  {
    unsigned i = index;
    for(unsigned iteration=0; iteration<max_iterations; iteration++)
    {
#if DEBUG
      std::cout << "iteration " << iteration << std::endl;
#endif
      //update abstract values
      bool converged = true;
      for(i=index; i<strategy.size(); i++)
      {
        converged = converged &&
          process_strategy_node(strategy[i].node, result, widen, edges_to_process);
        if(strategy[i].loop_head_index==index) break;
      }

      if(converged) 
      {
        index = ++i; 
        return true; //converged
      }
    }

    index = ++i; 
    return false; //not converged
  }

  bool process_strategy_node(Node n, resultt &result, bool widen,
    edges_to_processt &edges_to_process)
  {
#if DEBUG
    std::cout << "processing node " << n << std::endl;
#endif

    //update abstract value for node
    AbstractValue newv = result[n];
    edgest preds = edges_to_process[n];
    
    bool change=false;
    for(typename edgest::iterator e = preds.begin(); e!=preds.end(); e++) 
    {
      AbstractValue v = domain.transform(result[cfg.get_pred_node(*e)],
					                               cfg.get_transformer(*e));
      change=domain.join(newv,v)||change;
    }
    
    edges_to_process[n].clear();

    if(change)
    {
      //widening
      if(widen)
      {
        if(domain.widen(result[n],newv))
          return true; 
        else
          result[n] = newv;
      }
      
      //update worklist
      typename edges_to_processt::mapped_type succs=cfg.get_succ_edges(n);
      for(typename edges_to_processt::mapped_type::iterator e = succs.begin(); e!=succs.end(); e++) 
      {
        edges_to_process[cfg.get_succ_node(*e)].insert(*e);
      }  
      return false;
    }
    
    return true;
  }

};

#endif
