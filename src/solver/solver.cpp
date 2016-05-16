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
#include <util/arith_tools.h>

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

Function: solvert::add

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

unsigned solvert::add(const exprt &expr)
{
  exprt tmp=expr;
  simplify(tmp, ns);
  return add_rec(tmp);
}

/*******************************************************************\

Function: solvert::add_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

unsigned solvert::add_rec(const exprt &expr)
{
  // we do a mild bit of canonicalization
  
  if(expr.id()==ID_ge)
  {
    // rewrite x>=y to y<=x
    exprt tmp=expr;
    tmp.id(ID_le);
    assert(tmp.operands().size()==2);
    std::swap(tmp.op0(), tmp.op1());
    return add_rec(tmp);
  }
  else if(expr.id()==ID_gt)
  {
    // rewrite x>y to y<x
    exprt tmp=expr;
    tmp.id(ID_lt);
    assert(tmp.operands().size()==2);
    std::swap(tmp.op0(), tmp.op1());
    return add_rec(tmp);
  }

  unsigned old_size=expr_numbering.size();
  unsigned nr=expr_numbering(expr);
  
  // new? do recursion
  if(expr_numbering.size()!=old_size) new_expression(nr);

  return nr;
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
  
  numbering<exprt>::number_type a_nr, b_nr;
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
    dest[i]=add_rec(expr_op[i]);

  // store    
  expr_map[nr].op=dest;

  // Remember that the operands are contained in the expresion.
  for(unsigned i=0; i<dest.size(); i++)
    expr_map[dest[i]].operand_of.push_back(nr);
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
    // we record x!=y <=> !x==y
    set_equal(not_exprt(equal_exprt(expr.op0(), expr.op1())),
              expr);
  }
  else if(expr.id()==ID_equal)
  {
    add_operands(nr);
    equal_list.push_back(nr);
  }
  else if(expr.id()==ID_address_of)
  {
    // NOT an uninterpreted function, but rather a constant.
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
    
    // rummage through things that are equal to 'true'
    // and that we haven't processed yet

    for(unsigned i=0; i<equalities.size(); i++)
    {
      if(!is_true(i)) continue;
      if(expr_map[i].predicate_processed) continue;

      // remember we have done it
      expr_map[i].predicate_processed=true;
      
      const exprt &expr=expr_numbering[i];
      
      #ifdef DEBUG
      std::cout << "RUMMAGE true: " << from_expr(ns, "", expr) << std::endl;
      #endif
      
      if(expr.id()==ID_equal)
      {
        const equal_exprt &equal_expr=to_equal_expr(expr);
        const exprt &lhs=equal_expr.lhs();
        const exprt &rhs=equal_expr.rhs();
      
        implies_equal(add(lhs), add(rhs), progress);
      }
      else if(expr.id()==ID_le)
      {
        assert(expr.operands().size()==2);
        
        if(expr.op0().is_constant()) // c <= something
          bound(to_constant_expr(expr.op0()), expr.op1(), WEAK, LOWER, progress);
        else if(expr.op1().is_constant()) // something <= c
          bound(to_constant_expr(expr.op1()), expr.op0(), WEAK, UPPER, progress);
      }
      else if(expr.id()==ID_lt)
      {
        if(expr.op0().is_constant()) // c < something
          bound(to_constant_expr(expr.op0()), expr.op1(), STRICT, LOWER, progress);
        else if(expr.op1().is_constant()) // something < c
          bound(to_constant_expr(expr.op1()), expr.op0(), STRICT, UPPER, progress);
      }
    }

    // rummage through things that are equal to 'false'
    // and that we haven't processed yet

    for(unsigned i=0; i<equalities.size(); i++)
    {
      if(!is_false(i)) continue;
      if(expr_map[i].predicate_processed) continue;

      // remember we have done it
      expr_map[i].predicate_processed=true;
      
      const exprt &expr=expr_numbering[i];
      
      #ifdef DEBUG
      std::cout << "RUMMAGE false: " << from_expr(ns, "", expr) << std::endl;
      #endif
      
      if(expr.id()==ID_equal)
      {
        const equal_exprt &equal_expr=to_equal_expr(expr);
        const exprt &lhs=equal_expr.lhs();
        const exprt &rhs=equal_expr.rhs();
      
        implies_disequal(add(lhs), add(rhs), progress);
      }
      else if(expr.id()==ID_le)
      {
        assert(expr.operands().size()==2);
        
        if(expr.op0().is_constant()) // ! c <= something
          bound(to_constant_expr(expr.op0()), expr.op1(), STRICT, UPPER, progress);
        else if(expr.op1().is_constant()) // ! something <= c
          bound(to_constant_expr(expr.op1()), expr.op0(), STRICT, LOWER, progress);
      }
      else if(expr.id()==ID_lt)
      {
        if(expr.op0().is_constant()) // ! c < something
          bound(to_constant_expr(expr.op0()), expr.op1(), WEAK, UPPER, progress);
        else if(expr.op1().is_constant()) // ! something < c
          bound(to_constant_expr(expr.op1()), expr.op0(), WEAK, LOWER, progress);
      }
    }

    // Add bounds around constants.
    for(unsigned i=0; i<expr_numbering.size(); i++)
    {
      const exprt &e=expr_numbering[i];
      if(e.is_constant())
      {
        bound(to_constant_expr(e), e, WEAK, LOWER, progress);
        bound(to_constant_expr(e), e, WEAK, UPPER, progress);
      }
    }

    // Rummage through things that are equal,
    // and make the bounds meet. Should really use triggers for this.

    // References below aren't stable, thus enlarge now!
    integer_intervals[expr_numbering.size()-1];
    ieee_float_intervals[expr_numbering.size()-1];

    for(unsigned i=0; i<expr_numbering.size(); i++)
    {
      unsigned root=equalities.find(i);
      if(root==i) continue;
      if(integer_intervals[root].meet(integer_intervals[i])) progress=true;
      if(integer_intervals[i].meet(integer_intervals[root])) progress=true;
      if(ieee_float_intervals[root].meet(ieee_float_intervals[i])) progress=true;
      if(ieee_float_intervals[i].meet(ieee_float_intervals[root])) progress=true;
    }

    for(solver_expr_listt::const_iterator
        if_it=if_list.begin();
        if_it!=if_list.end();
        if_it++)
    {
      unsigned e_nr=*if_it;
      const solver_exprt &se=expr_map[e_nr];

      if(is_false(se.op[0])) // false ? x : y == y
      {
        implies_equal(se.op[2], e_nr, progress);
      }
      else if(is_true(se.op[0])) // true ? x : y == x
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

      if(is_false(se.op[1])) // x || false == x
      {
        implies_equal(se.op[0], e_nr, progress);
      }

      if(is_false(se.op[0])) // false || x == x
      {
        implies_equal(se.op[1], e_nr, progress);
      }

      if(is_true(se.op[1])) // x || true == true
      {
        implies_equal(true_nr, e_nr, progress);
      }

      if(is_true(se.op[0])) // true || x == true
      {
        implies_equal(true_nr, e_nr, progress);
      }

      if(is_false(e_nr)) // !(x || y) ===> !x, !y
      {
        for(unsigned i=0; i<se.op.size(); i++)
          implies_equal(se.op[i], false_nr, progress);
      }
    }

    for(solver_expr_listt::const_iterator
        and_it=and_list.begin();
        and_it!=and_list.end();
        and_it++)
    {
      unsigned e_nr=*and_it;
      const solver_exprt &se=expr_map[e_nr];

      if(is_true(se.op[1])) // x && true == x
      {
        implies_equal(se.op[0], e_nr, progress);
      }
      
      if(is_true(se.op[0])) // true && x == x
      {
        implies_equal(se.op[1], e_nr, progress);
      }

      if(is_false(se.op[1])) // x && false == false
      {
        implies_equal(false_nr, e_nr, progress);
      }
      
      if(is_false(se.op[0])) // false && x == false
      {
        implies_equal(false_nr, e_nr, progress);
      }

      if(is_true(e_nr)) // a && b == true -> a==true && b==true
      {
        for(std::vector<unsigned>::const_iterator
            o_it=se.op.begin(); o_it!=se.op.end(); o_it++)
          implies_equal(*o_it, true_nr, progress);
      }
    }

    for(solver_expr_listt::const_iterator
        not_it=not_list.begin();
        not_it!=not_list.end();
        not_it++)
    {
      unsigned e_nr=*not_it;
      const solver_exprt &se=expr_map[e_nr];

      if(is_true(se.op[0])) // !true == false
      {
        implies_equal(false_nr, e_nr, progress);
      }
      else if(is_false(se.op[0])) // !false == true
      {
        implies_equal(true_nr, e_nr, progress);
      }

      if(is_true(e_nr)) // !true == false
      {
        implies_equal(false_nr, se.op[0], progress);
      }
      else if(is_false(e_nr)) // !false == true
      {
        implies_equal(true_nr, se.op[0], progress);
      }
    }

    for(solver_expr_listt::const_iterator
        equal_it=equal_list.begin();
        equal_it!=equal_list.end();
        equal_it++)
    {
      unsigned e_nr=*equal_it;
      const solver_exprt &se=expr_map[e_nr];
      
      unsigned op0=equalities.find(se.op[0]);
      unsigned op1=equalities.find(se.op[1]);

      // Is it equal?
      if(is_equal(op0, op1))
        implies_equal(true_nr, e_nr, progress);
      
      // Is there a disequality for this equality?
      for(disequalitiest::const_iterator
          d_it=disequalities.begin();
          d_it!=disequalities.end();
          d_it++)
      {
        const std::set<unsigned> &diseq_set=d_it->second;
      
        for(std::set<unsigned>::const_iterator
            diseq_it=diseq_set.begin(); diseq_it!=diseq_set.end(); diseq_it++)
        {
          if(is_equal(d_it->first, op0) &&
             is_equal(*diseq_it, op1))
          {
            implies_equal(false_nr, e_nr, progress);
          }
          else if(is_equal(d_it->first, op1) &&
                  is_equal(*diseq_it, op0))
          {
            implies_equal(false_nr, e_nr, progress);
          }
        }
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
                      << e_nr1 << " = " << e_nr2 << "\n";
            #endif
            implies_equal(e_nr1, e_nr2, progress);
          }
        }
      }
    }
  }
  while(progress);
  
  // check if we are consistent
  
  if(is_equal(true_nr, false_nr))
    return D_UNSATISFIABLE;

  for(disequalitiest::const_iterator
      d_it=disequalities.begin();
      d_it!=disequalities.end();
      d_it++)
  {
    const std::set<unsigned> &diseq_set=d_it->second;
  
    for(std::set<unsigned>::const_iterator
        diseq_it=diseq_set.begin(); diseq_it!=diseq_set.end(); diseq_it++)
    {
      if(is_equal(d_it->first, *diseq_it))
        return D_UNSATISFIABLE;
    }
  }
  
  for(unsigned i=0; i<expr_numbering.size(); i++)
  {
    if(integer_intervals[i].is_bottom()) return D_UNSATISFIABLE;
    if(ieee_float_intervals[i].is_bottom()) return D_UNSATISFIABLE;
  }

  return D_SATISFIABLE;
}

/*******************************************************************\

Function: solvert::set_to

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void solvert::set_to(const exprt &expr, bool value)
{
  exprt tmp=expr;
  simplify(tmp, ns);
  set_to_rec(tmp, value);
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
    
    unsigned a=add(equal_expr.lhs()), b=add(equal_expr.rhs());

    if(value)
      set_equal(a, b);
    else
      set_disequal(a, b);
  }
  else if(expr.id()==ID_notequal)
  {
    // flip-image of the case above
    
    const notequal_exprt &notequal_expr=to_notequal_expr(expr);
    
    unsigned a=add(notequal_expr.lhs()), b=add(notequal_expr.rhs());

    if(value)
      set_disequal(a, b);
    else
      set_equal(a, b);
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
    // just treat as generic predicate
    set_equal(add(expr), value?true_nr:false_nr);
  }
}
  
/*******************************************************************\

Function: solvert::bound

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void solvert::bound(
  const constant_exprt &bound,
  const exprt &what,
  weak_strictt weak_strict,
  lower_uppert lower_upper,
  bool &progress)
{
  const typet &type=bound.type();
  
  if(type.id()==ID_signedbv || type.id()==ID_unsignedbv)
  {
    mp_integer int_val;
    if(to_integer(bound, int_val)) return;
    
    if(weak_strict==STRICT)
    {
      if(lower_upper==LOWER)
        ++int_val; // c < x ==> c+1 <= x
      else
        --int_val; // x < c ==> x <= c-1
    }
    
    integer_intervalt new_interval;
    
    if(lower_upper==LOWER)
      new_interval.set_lower(int_val);
    else
      new_interval.set_upper(int_val);

    integer_intervalt &interval=integer_intervals[add(what)];
    
    if(interval.meet(new_interval))
      progress=true;
  }
  else if(type.id()==ID_floatbv)
  {
    ieee_floatt float_val(bound);
    if(weak_strict!=WEAK) return;

    ieee_float_intervalt new_interval;
    
    if(lower_upper==LOWER)
      new_interval.set_lower(float_val);
    else
      new_interval.set_upper(float_val);

    ieee_float_intervalt &interval=ieee_float_intervals[add(what)];

    if(interval.meet(new_interval))
      progress=true;
  }
}

/*******************************************************************\

Function: solvert::is_a_constant

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool solvert::is_a_constant(const exprt &expr) const
{
  if(expr.is_constant()) return true;
  
  if(expr.id()==ID_address_of &&
     expr.operands().size()==1 &&
     expr.op0().id()==ID_symbol)
    return true;

  return false;
}

/*******************************************************************\

Function: solvert::get

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt solvert::get(const exprt &expr) const
{
  // is it already a constant?
  if(expr.is_constant())
    return expr;
  
  // is it an equality?
  if(expr.id()==ID_equal)
  {
    if(is_equal(to_equal_expr(expr).lhs(),
                to_equal_expr(expr).rhs()))
      return true_exprt();
  }
  else if(expr.id()==ID_not ||
          expr.id()==ID_and ||
          expr.id()==ID_or ||
          expr.id()==ID_implies)
  {
    exprt tmp=expr;
    Forall_operands(it, tmp)
      *it=get(*it); // recursive call
    return tmp;
  }
  
  exprt tmp=expr;
  simplify(tmp, ns);

  numbering<exprt>::number_type nr;

  if(!expr_numbering.get_number(tmp, nr))
  {
    // Equal to some constant?
    for(unsigned i=0; i<equalities.size(); i++)
      if(i!=nr &&
         is_equal(i, nr) &&
         is_a_constant(expr_numbering[i]))
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
  // equalities
  
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
  
  // disequalities
  
  for(disequalitiest::const_iterator
      d_it=disequalities.begin();
      d_it!=disequalities.end();
      d_it++)
  {
    const std::set<unsigned> &diseq_set=d_it->second;
  
    for(std::set<unsigned>::const_iterator
        diseq_it=diseq_set.begin(); diseq_it!=diseq_set.end(); diseq_it++)
    {
      out << "Disequal: "
          << from_expr(ns, "", expr_numbering[d_it->first])
          << " != "
          << from_expr(ns, "", expr_numbering[*diseq_it])
          << "\n";
    }
  }
  
  // intervals

  for(integer_intervalst::const_iterator
      i_it=integer_intervals.begin();
      i_it!=integer_intervals.end(); i_it++)
  {
    const integer_intervalt &interval=*i_it;
    
    if(interval.is_top()) continue;
    
    out << "Integer interval: ";

    if(interval.lower_set)
      out << interval.lower << " <= ";

    out << from_expr(ns, "", expr_numbering[i_it-integer_intervals.begin()]);
    
    if(interval.upper_set)
      out << " <= " << interval.upper;

    if(interval.is_bottom()) out << " (bottom)";
    
    out << "\n";
  }

  for(ieee_float_intervalst::const_iterator
      i_it=ieee_float_intervals.begin();
      i_it!=ieee_float_intervals.end(); i_it++)
  {
    const ieee_float_intervalt &interval=*i_it;
    
    if(interval.is_top()) continue;
    
    out << "Floating-point interval: ";

    if(interval.lower_set)
      out << interval.lower << " <= ";

    out << from_expr(ns, "", expr_numbering[i_it-ieee_float_intervals.begin()]);
    
    if(interval.upper_set)
      out << " <= " << interval.upper;
    
    if(interval.is_bottom()) out << " (bottom)";
    
    out << "\n";
  }

}
  
