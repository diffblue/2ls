/*******************************************************************\

Module: Summary Checker Base

Author: Peter Schrammel

\*******************************************************************/

#include <iostream>
#include <fstream>

#include <util/options.h>
#include <util/i2string.h>
#include <util/simplify_expr.h>
#include <langapi/language_util.h>
#include <util/prefix.h>
#include <goto-programs/write_goto_binary.h>

#include <solvers/sat/satcheck.h>
#include <solvers/flattening/bv_pointers.h>
#include <solvers/prop/literal_expr.h>

#include <ssa/local_ssa.h>
#include <ssa/simplify_ssa.h>
#include <ssa/ssa_build_goto_trace.h>
#include <domains/ssa_analyzer.h>
#include <ssa/ssa_unwinder.h>

#include <solver/summarizer_fw.h>
#include <solver/summarizer_fw_term.h>
#include <solver/summarizer_bw.h>
#include <solver/summarizer_bw_term.h>

#ifdef SHOW_CALLING_CONTEXTS
#include <solver/summarizer_fw_contexts.h>
#endif

#include "show.h"
#include "instrument_goto.h"

#include "summary_checker_base.h"

/*******************************************************************\

Function: summary_checker_baset::SSA_functions

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

///////////////////////////////////ic3////////////////////////////////
std::string extract_var(std::string in)
{
    std::string::iterator i;
    std::string s="";
    for(i=in.begin();*i!='#';i++)
    {
        s.append(1,*i);
    }
    return s;
}

int is_var(std::vector<exprt> vars,std::string in)
{
    std::string var;
    if(in.at(0)=='$')
        return -1;
    else
    {
        std::string::iterator i;
        int count=-1,pos=-1;
        for(i=in.begin();i!=in.end();i++)
        {
            if(*i=='#')
            {
                std::vector<exprt>::iterator i1;
                for(i1=vars.begin();i1!=vars.end();i1++)
                {
        std::string var1=extract_var(from_expr(*i1));
                    count++;
                    if(var.compare(var1)==0) pos=count;
                }
                if(pos==-1) return pos;
            }
            var.append(1,*i);
        }
        return pos;
    }
}
bool construct_cnf(std::vector<std::string>& P,std::ofstream& out,std::string in,std::vector<exprt> pre_vars,unsigned loophead)//reads the input formula and construct an cnf object
{
    int flag=0,sign=0,size=0;
    std::string::iterator i;
    std::string *s=new std::string(),*clause=new std::string(pre_vars.size(),'X');
    for (i=in.begin();i!=in.end();i++)
    {
        if(*i=='&')
        {
      std::vector<exprt>::iterator i1;
            if((s->compare("True")==0&&sign==0)||(s->compare("False")==0&&sign==1))
      {
    s->clear();
    clause->insert(0,'X',pre_vars.size());
    size=0;
    continue;
      }
      else if((s->compare("False")==0&&sign==0)||(s->compare("True")==0&&sign==1))
      {
    if(size==0)
    {
        P.clear();
        out<<"P is FALSE.\n";
        return false;
    }
      }
      else
      {
    std::vector<exprt>::iterator i1;
    int pos=0;
    *s=*s+"#phi"+std::to_string(loophead);
                for(i1=pre_vars.begin();i1!=pre_vars.end();i1++)
                {
                    if(from_expr(*i1).compare(*s)==0) 
        {
      if(sign==0 && clause->at(pos)!='F') (*clause)[pos]='T';
      else if(clause->at(pos)!='T') (*clause)[pos]='F';
      else
      {
          out<<"Contradiction in I.\n";
          return false;
      }
      break;
        }
        pos++;
                }
    sign=0;
    if(pos==pre_vars.size()) return false;
    P.push_back(*clause);
    s->clear();
    clause=new std::string(pre_vars.size(),'X');
    size=0;
      }
        }
        else if(*i=='|')
        {
            std::vector<exprt>::iterator i1;
            if((s->compare("True")==0&&sign==0)||(s->compare("False")==0&&sign==1))
      {
    while(*i!='&'||i!=in.end())
    {
        i++;
    }
    i--;
    clause->insert(0,'X',pre_vars.size());
    size=0;
      }
      else if((s->compare("False")==0&&sign==0)||(s->compare("True")==0&&sign==1))
      {
    
      }
      else
      {
    std::vector<exprt>::iterator i1;
    int pos=0;
    *s=*s+"#phi"+std::to_string(loophead);
                for(i1=pre_vars.begin();i1!=pre_vars.end();i1++)
                {
                    if(from_expr(*i1).compare(*s)==0) 
        {
      if(sign==0 && clause->at(pos)!='F') (*clause)[pos]='T';
      else if(clause->at(pos)!='T') (*clause)[pos]='F';
      else
      {
          out<<"Contradiction in I.\n";
          return false;
      }
      break;
        }
        pos++;
                }
    sign=0;
    if(pos==pre_vars.size()) return false;
      }
      s->clear();
  }
  else if(*i == '(')
  {
      if(!(s->empty()))
      {
    out<<"Error in the formula\n";
    return false;
      }
      if(flag==1)
      {
    out<<"Parenthesis mismatch\n";
    return false;
      }
      flag=1;
  }
  else if(*i == ')')
  {
      if(flag==0)
      {
    out<<"Parenthesis mismatch\n";
    return false;
      }
      flag=0;
  }
        else if(*i == '~') sign=1;
  else
  {
      s->append(1,*i);
  }
    }
    if(flag!=0){
  out<<"Parenthesis mismatch\n";
  return false;
    }
    std::vector<exprt>::iterator i1;
    if((s->compare("True")==0&&sign==0)||(s->compare("False")==0&&sign==1))
    {

    }
    else if((s->compare("False")==0&&sign==0)||(s->compare("True")==0&&sign==1))
    {
  if(size==0)
  {
      P.clear();
      out<<"P is FALSE.\n";
      return false;
  }
    }
    else
    {
  std::vector<exprt>::iterator i1;
  int pos=0;
  *s=*s+"#phi"+std::to_string(loophead);
  for(i1=pre_vars.begin();i1!=pre_vars.end();i1++)
  {
      if(from_expr(*i1).compare(*s)==0) 
      {
    if(sign==0 && clause->at(pos)!='F') (*clause)[pos]='T';
    else if(clause->at(pos)!='T') (*clause)[pos]='F';
    else
    {
        out<<"Contradiction in I.\n";
        return false;
    }   
    break;
      }
      pos++;
  }
  if(pos==pre_vars.size()) return false;
  P.push_back(*clause);
    }
    if(P.empty())
    {
  clause->clear();
  out<<"Property is True.\n";
  P.clear();
  return false;
    }
    return true;
}

exprt clause_to_exprt(std::string clause,std::vector<exprt> vars)
{
    std::vector<exprt> lits;
    unsigned i2;
    constant_exprt f("00000000",vars.at(0).type());
    for(i2 = 0;i2<clause.size();i2++)
    {
        //std::cout<<clause.size()<<std::endl;
        if(clause.at(i2)=='F')
        {
      lits.push_back(equal_exprt(vars.at(i2),f));
  }
  else if(clause.at(i2)=='T')
  {
            lits.push_back(notequal_exprt(vars.at(i2),f));
  }
    }
    return disjunction(lits);
}
std::vector<exprt> to_exprt_vec(std::vector<std::string> P,std::vector<exprt> vars)//adds clauses of the caller cnf to the Solver object
{
    std::vector<exprt> conjuncts;
    std::vector< std::string >::iterator i1;
    for(i1 = P.begin();i1 != P.end();i1++) 
    {
  conjuncts.push_back(clause_to_exprt(*i1,vars));
  //std::cout<<"\n";
    }
    //std::cout<<"solver::"<<from_expr(conjunction(conjuncts));
    return conjuncts;
}

bool subsumes(std::string cls1,std::string cls2)
{
    int i,cls_size=cls1.length();
    for(i=0;i<cls_size;i++)
    {
  if(cls1.at(i)!='X' && cls1.at(i)!=cls2.at(i)) return false;
    }
    return true;
}

bool block_recursively(std::ofstream& out,exprt I,exprt T,exprt CTI,std::vector<std::vector<std::string>> &Frames,int no,std::vector<exprt> pre_vars,std::vector<exprt> post_vars,const namespacet &ns,unsigned loophead)
{
    constant_exprt f("00000000",pre_vars.at(0).type());
    incremental_solvert solver(ns),solver1(ns);
    solver<<conjunction(to_exprt_vec(Frames.at(no),pre_vars));
    solver<<T;
    solver<<CTI;
    int count=1;
    while(solver()==decision_proceduret::D_SATISFIABLE)
    {
  std::string blocked_clause(pre_vars.size(),'X');
  std::vector<exprt> conjuncts,disjuncts;
        std::vector<exprt>::iterator iter;
  out<<"At frame "<<no+1<<"==>\n";
  int pos=0;
        for(iter=pre_vars.begin();iter!=pre_vars.end();iter++)
        {
            exprt e1=solver.get(*iter);
            if(from_expr(ns,"",e1).compare("TRUE")==0)
            {
    disjuncts.push_back(equal_exprt(*iter,f));
    conjuncts.push_back(equal_exprt(post_vars.at(pos),e1));
                blocked_clause[pos]='F';
            }
            else if(from_expr(ns,"",e1).compare("FALSE")==0)
            {
    disjuncts.push_back(notequal_exprt(*iter,f));
    conjuncts.push_back(equal_exprt(post_vars.at(pos),e1));
                blocked_clause[pos]='T';
            }
      pos++;
        }
  out<<"  CTI "<<count<<"::"<<from_expr(conjunction(conjuncts))<<"\n";
        solver<<disjunction(disjuncts);
        if(no==0)
        {
      incremental_solvert solver1(ns);
            solver1<<I;
            solver1<<T;
            solver1<<conjunction(conjuncts);
            if(solver1()==decision_proceduret::D_SATISFIABLE)
            {
                out<<"Bad state is reachable from initial state\n";
                return false;
            }
        }
        else
        {
            if(!(block_recursively(out,I,T,conjunction(conjuncts),Frames,no-1,pre_vars,post_vars,ns,loophead)))
            {
                return false;
            }
        }
  int i;
        for(i=0;i<=no;i++)
        {
      bool subsumes_flag=false;
      for(std::vector<std::string>::iterator iter1=Frames.at(i).begin();iter1!=Frames.at(i).end();iter1++)
      {
    if(subsumes(*iter1,blocked_clause)) subsumes_flag=true;
      }
      if(!subsumes_flag) Frames.at(i).push_back(blocked_clause);
        }
  out<<"Blocked clause(Blocked upto frame "<<no+1<<"):: "<<from_expr(disjunction(disjuncts))<<"\n\n";
  count++;
    }
    return true;
}

/*bool is_equivalent(std::vector<std::string> frame1,std::vector<std::string> frame2)
{
    
}*/

bool propagate_clauses(std::ofstream& out,exprt T,std::vector<std::vector<std::string>> &Frames,std::vector<exprt> pre_vars,std::vector<exprt> post_vars,int framesize,const namespacet &ns)
{
    out<<"Propagation phase |-------------------------------------------->\n\n";
    int i1;
    for(i1=0;i1<=framesize;i1++)
    {
        std::vector<std::string> Clauses1=Frames.at(i1),Clauses2=Frames.at(i1+1);
  unsigned i2,i3;
        for(i2=0;i2<Clauses1.size();i2++)
        {
            bool flag=false;
            for(i3=0;i3<Clauses2.size();i3++)
            {
                if(!Clauses1.at(i2).compare(Clauses2.at(i3)))
                {
                    flag=true;
                }
            }
            if(!flag)
            {
                incremental_solvert solver(ns);
                solver<<conjunction(to_exprt_vec(Frames.at(i1),pre_vars));
    solver<<T;
                solver<<not_exprt(clause_to_exprt(Clauses1.at(i2),post_vars));
                if(solver()==decision_proceduret::D_UNSATISFIABLE)
                {
        out<<"Propagating clause "<<from_expr(clause_to_exprt(Clauses1.at(i2),post_vars));
        out<<" from Frame "<<i1+1<<" to Frame "<<i1+2<<"\n";
                    Frames.at(i1+1).push_back(Clauses1.at(i2));
                }
            }
        }
  out<<"\n";
    }
    if(Frames.at(framesize).size()==Frames.at(framesize+1).size())//is_equilvalent(Frames.at(framesize),Frames.at(framesize+1))
    {
        out<<"Frame "<<i1<<" and "<<"Frame "<<i1+1<<" are same.\n\nInvariant found!\n";
        return true;
    }
    out<<"After propagation phase::\n";
    return false;
}

void do_ic3(std::ofstream& out,local_SSAt &SSA, const namespacet &ns, const dstring name,exprt T,exprt I,std::vector<exprt> P_pre,std::vector<std::string> P,std::vector<exprt> pre_vars,std::vector<exprt> post_vars,unsigned loophead) 
{
    incremental_solvert solver(ns);
    solver<<I;
    solver<<not_exprt(conjunction(P_pre));
    if(solver()==decision_proceduret::D_SATISFIABLE)
    {
        out<<"Initial state violates the property\n";
        return;
    }
    incremental_solvert solver1(ns),solver2(ns);
    std::vector<exprt> P_post=to_exprt_vec(P,post_vars);
    solver1<<I;
    solver1<<T;
    solver1<<not_exprt(conjunction(P_post));
    if(solver1()==decision_proceduret::D_SATISFIABLE)
    {
        out<<"Bad state is reachable from initial state in one step\n";
        //out<<from_expr(solver1.get(post_vars[0]));
        //out<<from_expr(solver1.get(post_vars[1]));
        return;
    }
    std::vector<std::vector<std::string>> Frames;
    Frames.push_back(std::vector<std::string>(P));
    int iter=0;
    out<<"\n=======================IC3 iteration "<<iter<<"=============================="<<"\n\n";
    /*if(!(block_recursively(out,I,T,P,Frames,iter,pre_vars,post_vars,ns,loophead)))
    {
        return;
    }*/
    while(iter>=0)
    {
        incremental_solvert solver2(ns);
  solver2<<conjunction(to_exprt_vec(Frames.at(iter),pre_vars));
  solver2<<T;
  solver2<<not_exprt(conjunction(P_post));
  if(solver2()==decision_proceduret::D_SATISFIABLE)
  {
      out<<"Blocking phase |-------------------------------------------->\n\n";
      for(std::vector<exprt>::iterator i=P_post.begin();i!=P_post.end();i++)
      {
    if(!(block_recursively(out,I,T,not_exprt(*i),Frames,iter,pre_vars,post_vars,ns,loophead)))
    {
        return;
    }
      }
  }
        else
        {
            Frames.push_back(std::vector<std::string>());
            if(propagate_clauses(out,T,Frames,pre_vars,post_vars,iter,ns)) return;
      int i=0;
      while(i<=iter+1)
      {
    out<<"Frame"<<i<<"::  ";
    out<<from_expr(conjunction(to_exprt_vec(Frames.at(i),pre_vars)))<<"\n";
    i++;
      }
            iter++;
      out<<"\n=======================IC3 iteration "<<iter<<"=============================="<<"\n\n";
        }
    }
}

bool get_I_and_T(std::ofstream& out,local_SSAt &SSA,const namespacet &ns,std::vector<exprt>& pre_vars,std::vector<exprt>& post_vars,unsigned& loophead,exprt& I,exprt& T)
{
    std::vector<exprt> conjuncts,conjuncts1;
    unsigned loopend=0;
    loophead=0;
    for(local_SSAt::nodest::const_iterator n_it=SSA.nodes.begin();
      n_it!=SSA.nodes.end(); n_it++)
    {
        if(n_it->loophead!=SSA.nodes.end())
        {
            loophead=n_it->loophead->location->location_number;
            loopend=n_it->location->location_number;
            break;
        }
    }
    if(loophead==loopend&&loopend==0)
    {
        out<<"No loop in the program\n";
        return false;
    }
    for(local_SSAt::nodest::const_iterator n_it=SSA.nodes.begin();
      n_it!=SSA.nodes.end(); n_it++)
    {
        if(n_it->location->location_number==loophead)
        {
            exprt loop_exit_cond,temp_exp;
            for(local_SSAt::nodet::equalitiest::const_iterator c_it=n_it->equalities.begin();
              c_it!=n_it->equalities.end();
              c_it++)
            {
                pre_vars.push_back((*c_it).op0());
                loop_exit_cond=temp_exp;
                temp_exp=*c_it;
            }
            pre_vars.pop_back();
            pre_vars.pop_back();
            conjuncts.push_back(loop_exit_cond);
      conjuncts.push_back(equal_exprt(temp_exp.op0(),true_exprt()));
        }
    }
    exprt post_vars1[pre_vars.size()];
    for(local_SSAt::nodest::const_iterator n_it=SSA.nodes.begin();
      n_it!=SSA.nodes.end(); n_it++)
    {
  if(n_it->location->location_number<loophead)
  {
      for(local_SSAt::nodet::equalitiest::const_iterator c_it=n_it->equalities.begin();
              c_it!=n_it->equalities.end();
              c_it++)
            {
    conjuncts1.push_back(*c_it);
      }
  }
  else if(n_it->location->location_number==loophead)
  {
      for(local_SSAt::nodet::equalitiest::const_iterator c_it=n_it->equalities.begin();
              c_it!=n_it->equalities.end();
              c_it++)
            {
    conjuncts1.push_back(*c_it);
      }
      local_SSAt::nodet::equalitiest::const_iterator c_it=n_it->equalities.begin();
      conjuncts1.pop_back();
      conjuncts1.pop_back();
      conjuncts1.push_back(equal_exprt(c_it->op1().op0(),false_exprt()));
      I=conjunction(conjuncts1);
  }
        else if(n_it->location->location_number>loophead && n_it->location->location_number<=loopend)
        {
            for(local_SSAt::nodet::equalitiest::const_iterator c_it=n_it->equalities.begin();
              c_it!=n_it->equalities.end();
              c_it++)
            {
                int pos=is_var(pre_vars,from_expr(c_it->op0()));
                if(pos!=-1)
                {
                    post_vars1[pos]=c_it->op0();
                }
                conjuncts.push_back(*c_it);
            }
        }
    }
    unsigned j;
    for(j=0;j<pre_vars.size();j++)
    {
  symbol_exprt post_var(dstring(extract_var(from_expr(pre_vars.at(j)))+"#0"),pre_vars.at(0).type());
        conjuncts.push_back(equal_exprt(post_vars1[j],post_var));
  post_vars.push_back(post_var);
    }
    T=conjunction(conjuncts);
    return true;
}

void CustomSSAOperation(local_SSAt &SSA, const namespacet &ns, const dstring name)
{
    std::ofstream out("output.txt");
    out<<"//////////////////////Output of custom SSA Operation\\\\\\\\\\\\\\\\\\\\\\\\\\\\\n\n\n";
    std::vector<exprt> pre_vars,post_vars;
    unsigned loophead=0;
    exprt I,T;
    if(!get_I_and_T(out,SSA,ns,pre_vars,post_vars,loophead,I,T)) return;
    out<<"T:= "<<from_expr(ns," ",T)<<std::endl;
    out<<"\nI:= "<<from_expr(ns," ",I)<<std::endl;
    
    std::cout<<"Give the property in CNF form(don't use space in the formula):\n";
    std::string prop;
    std::cin>>prop;
    std::vector<std::string> P;
    if(!construct_cnf(P,out,prop,pre_vars,loophead))
    {
        out<<"Error in the given property\n";
        return;
    }
    std::vector<exprt> P_pre=to_exprt_vec(P,pre_vars);
    out<<"\nP:= "<<from_expr(conjunction(P_pre))<<"\n\n";
    do_ic3(out,SSA,ns,name,T,I,P_pre,P,pre_vars,post_vars,loophead);
    out.close();
}
///////////////////////////////////ic3////////////////////////////////

void summary_checker_baset::SSA_functions(
  const goto_modelt &goto_model,
  const namespacet &ns,
  const ssa_heap_analysist &heap_analysis)
{
  // compute SSA for all the functions
  forall_goto_functions(f_it, goto_model.goto_functions)
  {
    if(!f_it->second.body_available())
      continue;
    if(has_prefix(id2string(f_it->first), TEMPLATE_DECL))
      continue;
    status() << "Computing SSA of " << f_it->first << messaget::eom;

    ssa_db.create(f_it->first, f_it->second, ns, heap_analysis);
    local_SSAt &SSA=ssa_db.get(f_it->first);

    // simplify, if requested
    if(simplify)
    {
      status() << "Simplifying" << messaget::eom;
      ::simplify(SSA, ns);
    }

    SSA.output(debug()); debug() << eom;
  }

  // properties
  initialize_property_map(goto_model.goto_functions);
  //CustomSSAOperation(SSA,ns,"");//execute ic3
}

/*******************************************************************\

Function: summary_checker_baset::summarize

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void summary_checker_baset::summarize(
  const goto_modelt &goto_model,
  bool forward,
  bool termination)
{
  summarizer_baset *summarizer=NULL;

#ifdef SHOW_CALLING_CONTEXTS
  if(options.get_bool_option("show-calling-contexts"))
    summarizer=new summarizer_fw_contextst(
      options, summary_db, ssa_db, ssa_unwinder, ssa_inliner);
  else // NOLINT(*)
#endif
  {
    if(forward && !termination)
      summarizer=new summarizer_fwt(
        options, summary_db, ssa_db, ssa_unwinder, ssa_inliner);
    if(forward && termination)
      summarizer=new summarizer_fw_termt(
        options, summary_db, ssa_db, ssa_unwinder, ssa_inliner);
    if(!forward && !termination)
      summarizer=new summarizer_bwt(
        options, summary_db, ssa_db, ssa_unwinder, ssa_inliner);
    if(!forward && termination)
      summarizer=new summarizer_bw_termt(
        options, summary_db, ssa_db, ssa_unwinder, ssa_inliner);
  }
  assert(summarizer!=NULL);

  summarizer->set_message_handler(get_message_handler());

  if(!options.get_bool_option("context-sensitive") &&
     options.get_bool_option("all-functions"))
    summarizer->summarize();
  else
    summarizer->summarize(goto_model.goto_functions.entry_point());

  // statistics
  solver_instances+=summarizer->get_number_of_solver_instances();
  solver_calls+=summarizer->get_number_of_solver_calls();
  summaries_used+=summarizer->get_number_of_summaries_used();
  termargs_computed+=summarizer->get_number_of_termargs_computed();

  delete summarizer;
}
/*******************************************************************\

Function: summary_checker_baset::check_properties

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

summary_checker_baset::resultt summary_checker_baset::check_properties()
{
  // analyze all the functions
  for(ssa_dbt::functionst::const_iterator f_it=ssa_db.functions().begin();
      f_it!=ssa_db.functions().end(); f_it++)
  {
    status() << "Checking properties of " << f_it->first << messaget::eom;

#if 0
    // for debugging
    show_ssa_symbols(*f_it->second, std::cerr);
#endif

    check_properties(f_it);

    if(options.get_bool_option("show-invariants"))
    {
      if(!summary_db.exists(f_it->first))
        continue;
      show_invariants(*(f_it->second), summary_db.get(f_it->first), result());
      result() << eom;
    }
  }

  summary_checker_baset::resultt result=property_checkert::PASS;
  for(property_mapt::const_iterator
        p_it=property_map.begin(); p_it!=property_map.end(); p_it++)
  {
    if(p_it->second.result==FAIL)
      return property_checkert::FAIL;
    if(p_it->second.result==UNKNOWN)
      result=property_checkert::UNKNOWN;
  }

  return result;
}

/*******************************************************************\

Function: summary_checker_baset::check_properties

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void summary_checker_baset::check_properties(
  const ssa_dbt::functionst::const_iterator f_it)
{
  unwindable_local_SSAt &SSA=*f_it->second;

  bool all_properties=options.get_bool_option("all-properties");

  SSA.output_verbose(debug()); debug() << eom;

  // incremental version

  // solver
  incremental_solvert &solver=ssa_db.get_solver(f_it->first);
  solver.set_message_handler(get_message_handler());

  // give SSA to solver
  solver << SSA;
  SSA.mark_nodes();

  solver.new_context();

  exprt enabling_expr=SSA.get_enabling_exprs();
  solver << enabling_expr;

  // invariant, calling contexts
  if(summary_db.exists(f_it->first))
  {
    solver << summary_db.get(f_it->first).fw_invariant;
    solver << summary_db.get(f_it->first).fw_precondition;

    if(options.get_bool_option("heap") &&
       summary_db.get(f_it->first).aux_precondition.is_not_nil())
    {
      solver << summary_db.get(f_it->first).aux_precondition;
    }
  }

  // callee summaries
  solver << ssa_inliner.get_summaries(SSA);

  // freeze loop head selects
  exprt::operandst loophead_selects=
    get_loophead_selects(f_it->first, SSA, *solver.solver);
  // check whether loops have been fully unwound
  exprt::operandst loop_continues=
    get_loop_continues(f_it->first, SSA, *solver.solver);
  bool fully_unwound=
    is_fully_unwound(loop_continues, loophead_selects, solver);
  status() << "Loops " << (fully_unwound ? "" : "not ")
           << "fully unwound" << eom;

  cover_goals_extt cover_goals(
    SSA, solver, loophead_selects, property_map,
    !fully_unwound && options.get_bool_option("spurious-check"),
    all_properties,
    options.get_bool_option("trace") ||
    options.get_option("graphml-witness")!="" ||
    options.get_option("json-cex")!="");

#if 0
  debug() << "(C) " << from_expr(SSA.ns, "", enabling_expr) << eom;
#endif

  const goto_programt &goto_program=SSA.goto_function.body;

  for(goto_programt::instructionst::const_iterator
        i_it=goto_program.instructions.begin();
      i_it!=goto_program.instructions.end();
      i_it++)
  {
    if(!i_it->is_assert())
      continue;

    const source_locationt &location=i_it->source_location;
    irep_idt property_id=location.get_property_id();

    if(i_it->guard.is_true())
    {
      property_map[property_id].result=PASS;
      continue;
    }

    // do not recheck properties that have already been decided
    if(property_map[property_id].result!=UNKNOWN)
      continue;

    // TODO: some properties do not show up in initialize_property_map
    if(property_id=="")
      continue;

    std::list<local_SSAt::nodest::const_iterator> assertion_nodes;
    SSA.find_nodes(i_it, assertion_nodes);

    unsigned property_counter=0;
    for(std::list<local_SSAt::nodest::const_iterator>::const_iterator
          n_it=assertion_nodes.begin();
        n_it!=assertion_nodes.end();
        n_it++)
    {
      for(local_SSAt::nodet::assertionst::const_iterator
            a_it=(*n_it)->assertions.begin();
          a_it!=(*n_it)->assertions.end();
          a_it++, property_counter++)
      {
        exprt property=*a_it;

        if(simplify)
          property=::simplify_expr(property, SSA.ns);

#if 0
        std::cout << "property: " << from_expr(SSA.ns, "", property)
                  << std::endl;
#endif

        property_map[property_id].location=i_it;
        cover_goals.goal_map[property_id].conjuncts.push_back(property);
      }
    }
  }

  for(cover_goals_extt::goal_mapt::const_iterator
        it=cover_goals.goal_map.begin();
      it!=cover_goals.goal_map.end();
      it++)
  {
    // Our goal is to falsify a property.
    // The following is TRUE if the conjunction is empty.
    literalt p=!solver.convert(conjunction(it->second.conjuncts));
    cover_goals.add(p);
  }

  status() << "Running " << solver.solver->decision_procedure_text() << eom;

  cover_goals();

  // set all non-covered goals to PASS except if we do not try
  //  to cover all goals and we have found a FAIL
  if(all_properties || cover_goals.number_covered()==0)
  {
    std::list<cover_goals_extt::cover_goalt>::const_iterator g_it=
      cover_goals.goals.begin();
    for(cover_goals_extt::goal_mapt::const_iterator
          it=cover_goals.goal_map.begin();
        it!=cover_goals.goal_map.end();
        it++, g_it++)
    {
      if(!g_it->covered)
        property_map[it->first].result=PASS;
    }
  }

  solver.pop_context();

  debug() << "** " << cover_goals.number_covered()
          << " of " << cover_goals.size() << " failed ("
          << cover_goals.iterations() << " iterations)" << eom;
}

/*******************************************************************\

Function: summary_checker_baset::report_statistics

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void summary_checker_baset::report_statistics()
{
  for(ssa_dbt::functionst::const_iterator f_it=ssa_db.functions().begin();
      f_it!=ssa_db.functions().end(); f_it++)
  {
    incremental_solvert &solver=ssa_db.get_solver(f_it->first);
    unsigned calls=solver.get_number_of_solver_calls();
    if(calls>0)
      solver_instances++;
    solver_calls+=calls;
  }
  statistics() << "** statistics: " << eom;
  statistics() << "  number of solver instances: " << solver_instances << eom;
  statistics() << "  number of solver calls: " << solver_calls << eom;
  statistics() << "  number of summaries used: "
               << summaries_used << eom;
  statistics() << "  number of termination arguments computed: "
               << termargs_computed << eom;
  statistics() << eom;
}

/*******************************************************************\

Function: summary_checker_baset::do_show_vcc

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void summary_checker_baset::do_show_vcc(
  const local_SSAt &SSA,
  const goto_programt::const_targett i_it,
  const local_SSAt::nodet::assertionst::const_iterator &a_it)
{
  std::cout << i_it->source_location << "\n";
  std::cout << i_it->source_location.get_comment() << "\n";

  std::list<exprt> ssa_constraints;
  ssa_constraints << SSA;

  unsigned i=1;
  for(std::list<exprt>::const_iterator c_it=ssa_constraints.begin();
      c_it!=ssa_constraints.end();
      c_it++, i++)
    std::cout << "{-" << i << "} " << from_expr(SSA.ns, "", *c_it) << "\n";

  std::cout << "|--------------------------\n";

  std::cout << "{1} " << from_expr(SSA.ns, "", *a_it) << "\n";

  std::cout << "\n";
}

/*******************************************************************\

Function: summary_checker_baset::get_loophead_selects

  Inputs:

 Outputs:

 Purpose: returns the select guards at the loop heads
          in order to check whether a countermodel is spurious

\*******************************************************************/

exprt::operandst summary_checker_baset::get_loophead_selects(
  const irep_idt &function_name,
  const local_SSAt &SSA, prop_convt &solver)
{
  // TODO: this should be provided by unwindable_local_SSA
  exprt::operandst loophead_selects;
  for(local_SSAt::nodest::const_iterator n_it=SSA.nodes.begin();
      n_it!=SSA.nodes.end(); n_it++)
  {
    if(n_it->loophead==SSA.nodes.end())
      continue;
    symbol_exprt lsguard=
      SSA.name(SSA.guard_symbol(), local_SSAt::LOOP_SELECT, n_it->location);
    ssa_unwinder.get(function_name).unwinder_rename(lsguard, *n_it, true);
    loophead_selects.push_back(not_exprt(lsguard));
    solver.set_frozen(solver.convert(lsguard));
  }
  literalt loophead_selects_literal=
    solver.convert(conjunction(loophead_selects));
  if(!loophead_selects_literal.is_constant())
    solver.set_frozen(loophead_selects_literal);

#if 0
  std::cout << "loophead_selects: "
            << from_expr(SSA.ns, "", conjunction(loophead_selects))
            << std::endl;
#endif

  return loophead_selects;
}

/*******************************************************************\

Function: summary_checker_baset::get_loop_continues

  Inputs:

 Outputs:

 Purpose: returns the loop continuation guards at the end of the
          loops in order to check whether we can unroll further

\*******************************************************************/

exprt::operandst summary_checker_baset::get_loop_continues(
  const irep_idt &function_name,
  const local_SSAt &SSA, prop_convt &solver)
{
  // TODO: this should be provided by unwindable_local_SSA
  exprt::operandst loop_continues;

  ssa_unwinder.get(function_name).loop_continuation_conditions(loop_continues);
  if(loop_continues.size()==0)
  {
    // TODO: this should actually be done transparently by the unwinder
    for(local_SSAt::nodest::const_iterator n_it=SSA.nodes.begin();
        n_it!=SSA.nodes.end(); n_it++)
    {
      if(n_it->loophead==SSA.nodes.end())
        continue;
      symbol_exprt guard=SSA.guard_symbol(n_it->location);
      symbol_exprt cond=SSA.cond_symbol(n_it->location);
      loop_continues.push_back(and_exprt(guard, cond));
    }
  }

#if 0
  std::cout << "loophead_continues: "
            << from_expr(SSA.ns, "", disjunction(loop_continues)) << std::endl;
#endif

  return loop_continues;
}

/*******************************************************************\

Function: summary_checker_baset::is_fully_unwound

  Inputs:

 Outputs:

 Purpose: checks whether the loops have been fully unwound

\*******************************************************************/

bool summary_checker_baset::is_fully_unwound(
  const exprt::operandst &loop_continues,
  const exprt::operandst &loophead_selects,
  incremental_solvert &solver)
{
  solver.new_context();
  solver <<
    and_exprt(conjunction(loophead_selects), disjunction(loop_continues));

  solver_calls++; // statistics

  switch(solver())
  {
  case decision_proceduret::D_SATISFIABLE:
    solver.pop_context();
    return false;
    break;

  case decision_proceduret::D_UNSATISFIABLE:
    solver.pop_context();
    solver << conjunction(loophead_selects);
    return true;
    break;

  case decision_proceduret::D_ERROR:
  default:
    throw "error from decision procedure";
  }
}

/*******************************************************************\

Function: summary_checker_baset::is_spurious

  Inputs:

 Outputs:

 Purpose: checks whether a countermodel is spurious

\*******************************************************************/

bool summary_checker_baset::is_spurious(
  const exprt::operandst &loophead_selects,
  incremental_solvert &solver)
{
  // check loop head choices in model
  bool invariants_involved=false;
  for(exprt::operandst::const_iterator l_it=loophead_selects.begin();
      l_it!=loophead_selects.end(); l_it++)
  {
    if(solver.get(l_it->op0()).is_true())
    {
      invariants_involved=true;
      break;
    }
  }
  if(!invariants_involved)
    return false;

  // force avoiding paths going through invariants
  solver << conjunction(loophead_selects);

  solver_calls++; // statistics

  switch(solver())
  {
  case decision_proceduret::D_SATISFIABLE:
    return false;
    break;

  case decision_proceduret::D_UNSATISFIABLE:
    return true;
    break;

  case decision_proceduret::D_ERROR:
  default:
    throw "error from decision procedure";
  }
}

/*******************************************************************\

Function: summary_checker_baset::instrument_and_output

  Inputs:

 Outputs:

 Purpose: instruments the code with the inferred information
          and outputs it to a goto-binary

\*******************************************************************/

void summary_checker_baset::instrument_and_output(goto_modelt &goto_model)
{
  instrument_gotot instrument_goto(options, ssa_db, summary_db);
  instrument_goto(goto_model);
  std::string filename=options.get_option("instrument-output");
  status() << "Writing instrumented goto-binary " << filename << eom;
  write_goto_binary(
    filename,
    goto_model.symbol_table,
    goto_model.goto_functions,
    get_message_handler());
}
