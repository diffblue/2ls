/*******************************************************************\

Module: Delta Checking Solver

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

//#define DEBUG

#ifdef DEBUG
#include <iostream>
#endif

#include <map>
#include <set>

#include <langapi/language_util.h>

#include <util/expr.h>
#include <util/std_expr.h>
#include <util/simplify_expr.h>

#include "solver.h"

/*******************************************************************\

Function: solvert::solvert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

solvert::solvert(const namespacet &_ns):decision_proceduret(_ns)
{
  false_nr=add(false_exprt());
  true_nr=add(true_exprt());
}

/*******************************************************************\

Function: solvert::simplify_and_add

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

unsigned solvert::simplify_and_add(const exprt &expr)
{
  exprt tmp=expr;
  simplify(tmp, ns);
  return add(tmp);
}

/*******************************************************************\

Function: solvert::is_equal

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool solvert::is_equal(const exprt &a, const exprt &b) const
{
  exprt tmp_a=a, tmp_b=b;
  
  simplify(tmp_a, ns);
  simplify(tmp_b, ns);
  
  unsigned a_nr, b_nr;
  if(expr_numbering.get_number(tmp_a, a_nr)) return false;
  if(expr_numbering.get_number(tmp_b, b_nr)) return false;
  return is_equal(a_nr, b_nr);
}

/*******************************************************************\

Function: solvert::add_operands

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void solvert::add_operands(unsigned nr)
{
  // expr_numbering is a vector, and thus not stable.
  // We will call add recursively below.
  const exprt expr=expr_numbering[nr];

  const exprt::operandst &expr_op=expr.operands();
  std::vector<unsigned> dest;

  dest.resize(expr_op.size());

  for(unsigned i=0; i<dest.size(); i++)
    dest[i]=add(expr_op[i]);

  // store    
  expr_map[nr].op=dest;
}

/*******************************************************************\

Function: solvert::new_expression

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void solvert::new_expression(unsigned nr)
{
  // expr_numbering is a vector, and thus not stable.
  const exprt expr=expr_numbering[nr];
      
  if(expr.id()==ID_if)
  {
    add_operands(nr);
    if_list.push_back(nr);
    
    // we also add if-s as UFs (uff!)
    uf_map[ID_if].push_back(nr);
  }
  else if(expr.id()==ID_or)
  {
    add_operands(nr);
    or_list.push_back(nr);
  }
  else if(expr.id()==ID_and)
  {
    add_operands(nr);
    and_list.push_back(nr);
  }
  else if(expr.id()==ID_not)
  {
    add_operands(nr);
    not_list.push_back(nr);
  }
  else if(expr.id()==ID_notequal)
  {
    #if 0
    // we record x!=y <=> !x==y
    set_equal(not_exprt(equal_exprt(expr.op0(), expr.op1())),
              expr);
    #endif
    assert(false);
  }
  else
  {
    if(expr.has_operands()) // make it uninterpreted
    {
      add_operands(nr);
      uf_map[expr.id()].push_back(nr);
      
      #ifdef DEBUG
      std::cout << "UF " << nr << " added: " << expr.id();
      forall_operands(it, expr) std::cout << " " << add(*it);
      std::cout << "\n";
      #endif
    }
  }
}

/*******************************************************************\

Function: solvert::dec_solve

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

decision_proceduret::resultt solvert::dec_solve()
{
  bool progress;
  
  do
  {  
    progress=false;

    for(solver_expr_listt::const_iterator
        if_it=if_list.begin();
        if_it!=if_list.end();
        if_it++)
    {
      unsigned e_nr=*if_it;
      const solver_exprt &se=expr_map[e_nr];

      if(is_equal(se.op[0], false_nr)) // false ? x : y == y
      {
        implies_equal(se.op[2], e_nr, progress);
      }
      else if(is_equal(se.op[0], true_nr)) // true ? x : y == x
      {
        implies_equal(se.op[1], e_nr, progress);
      }

      if(is_equal(se.op[2], se.op[1])) // c ? x : x == x
      {
        implies_equal(se.op[2], e_nr, progress);
      }
    }
    
    for(solver_expr_listt::const_iterator
        or_it=or_list.begin();
        or_it!=or_list.end();
        or_it++)
    {
      unsigned e_nr=*or_it;
      const solver_exprt &se=expr_map[e_nr];

      if(is_equal(se.op[1], false_nr)) // x || false == x
      {
        implies_equal(se.op[0], e_nr, progress);
      }
      else if(is_equal(se.op[0], false_nr)) // false || x == x
      {
        implies_equal(se.op[1], e_nr, progress);
      }
    }

    for(solver_expr_listt::const_iterator
        and_it=and_list.begin();
        and_it!=and_list.end();
        and_it++)
    {
      unsigned e_nr=*and_it;
      const solver_exprt &se=expr_map[e_nr];

      if(is_equal(se.op[1], true_nr)) // x || true == x
      {
        implies_equal(se.op[0], e_nr, progress);
      }
      else if(is_equal(se.op[0], true_nr)) // true || x == x
      {
        implies_equal(se.op[1], e_nr, progress);
      }
    }

    for(solver_expr_listt::const_iterator
        not_it=not_list.begin();
        not_it!=not_list.end();
        not_it++)
    {
      unsigned e_nr=*not_it;
      const solver_exprt &se=expr_map[e_nr];

      if(is_equal(se.op[0], true_nr)) // !true == false
      {
        implies_equal(false_nr, e_nr, progress);
      }
      else if(is_equal(se.op[0], false_nr)) // !false == true
      {
        implies_equal(true_nr, e_nr, progress);
      }

      if(is_equal(e_nr, true_nr)) // !true == false
      {
        implies_equal(false_nr, se.op[0], progress);
      }
      else if(is_equal(e_nr, false_nr)) // !false == true
      {
        implies_equal(true_nr, se.op[0], progress);
      }
    }

    for(uf_mapt::const_iterator
        uf_map_it=uf_map.begin();
        uf_map_it!=uf_map.end();
        uf_map_it++)
    {
      const solver_expr_listt &uf_list=uf_map_it->second;
    
      // boo, quadratic!
      for(solver_expr_listt::const_iterator
          uf_it1=uf_list.begin();
          uf_it1!=uf_list.end();
          uf_it1++)
      {
        solver_expr_listt::const_iterator next=uf_it1;
        next++;
      
        for(solver_expr_listt::const_iterator
            uf_it2=next;
            uf_it2!=uf_list.end();
            uf_it2++)
        {
          unsigned e_nr1=*uf_it1, e_nr2=*uf_it2;
          const solver_exprt &se1=expr_map[e_nr1], 
                             &se2=expr_map[e_nr2];

          // same number of arguments?        
          if(se1.op.size()!=se2.op.size()) continue;
          
          // already equal?
          if(is_equal(e_nr1, e_nr2)) continue;
          
          bool all_equal=true;
          
          for(unsigned i=0; i<se1.op.size(); i++)
          {
            if(!is_equal(se1.op[i], se2.op[i]))
            {
              #ifdef DEBUG
              std::cout << "UF check " 
                        << e_nr1 << " vs " << e_nr2
                        << ": op " << i << " not equal\n";
              #endif
              all_equal=false;
              break;
            }
          }
          
          if(all_equal)
          {
            #ifdef DEBUG
            std::cout << "UF check: " 
                      << uf_it1->e_nr << " = " << uf_it2->e_nr << "\n";
            #endif
            set_equal(e_nr1, e_nr2);
            progress=true;
          }
        }
      }
    }
  }
  while(progress);

  return D_ERROR;
}

/*******************************************************************\

Function: solvert::set_to

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

#include <iostream>

void solvert::set_to(const exprt &expr, bool value)
{
  exprt tmp=expr;
  simplify(tmp, ns);
  set_to_rec(tmp, value);
  
  std::cout << "SET TO " << value << ": " << from_expr(ns, "", expr) << std::endl;
}
  
/*******************************************************************\

Function: solvert::set_to_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void solvert::set_to_rec(const exprt &expr, bool value)
{
  if(expr.id()==ID_equal)
  {
    const equal_exprt &equal_expr=to_equal_expr(expr);

    if(value)
      set_equal(add(equal_expr.lhs()), add(equal_expr.rhs()));
  }
  else if(expr.id()==ID_notequal)
  {
    assert(false);
  }
  else if(expr.id()==ID_not)
  {
    set_to_rec(to_not_expr(expr).op(), !value);
  }
  else if(expr.id()==ID_and)
  {
    if(value)
    {
      forall_operands(it, expr)
        set_to_rec(*it, true);
    }
    else
      set_equal(add(expr), false_nr);
  }
  else
  {
    set_equal(add(expr), value?true_nr:false_nr);
  }
}
  
/*******************************************************************\

Function: solvert::get

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt solvert::get(const exprt &expr) const
{
  if(expr.is_constant()) return expr;
  
  // is it an equality?
  if(expr.id()==ID_equal)
  {
    if(is_equal(to_equal_expr(expr).lhs(),
                to_equal_expr(expr).rhs()))
      return true_exprt();
  }
  else if(expr.id()==ID_not ||
          expr.id()==ID_and ||
          expr.id()==ID_or)
  {
    exprt tmp=expr;
    Forall_operands(it, tmp)
      *it=get(*it); // recursive call
    return tmp;
  }
  
  exprt tmp=expr;
  simplify(tmp, ns);

  unsigned nr;

  if(!expr_numbering.get_number(tmp, nr))
  {
    // equal to some constant?
    for(unsigned i=0; i<equalities.size(); i++)
      if(expr_numbering[i].is_constant() &&
         is_equal(i, nr))
        return expr_numbering[i];
  }

  return nil_exprt();
}
  
/*******************************************************************\

Function: solvert::print_assignment

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void solvert::print_assignment(std::ostream &out) const
{
  std::map<unsigned, std::set<unsigned> > equality_map;
  
  for(unsigned i=0; i<expr_numbering.size(); i++)
    equality_map[equalities.find(i)].insert(i);
  
  for(std::map<unsigned, std::set<unsigned> >::const_iterator
      e_it=equality_map.begin();
      e_it!=equality_map.end();
      e_it++)
  {
    const std::set<unsigned> &eq_set=e_it->second;
  
    if(eq_set.size()>=2)
    {
      for(std::set<unsigned>::const_iterator
          eq_it=eq_set.begin(); eq_it!=eq_set.end(); eq_it++)
      {
        out << "Equal: "
            << from_expr(ns, "", expr_numbering[*eq_it]) << "\n";
      }

      out << "\n";
    }
  }
}
  
