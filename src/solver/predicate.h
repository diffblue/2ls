/*******************************************************************\

Module: Predicate Expressions and Types

Author: Peter Schrammel

\*******************************************************************/

#ifndef CPROVER_2LS_PREDICATE_H
#define CPROVER_2LS_PREDICATE_H

#include <set>

#include <util/std_expr.h>
#include <util/std_types.h>

class predicate_typet : public code_typet 
{
public:
  explicit predicate_typet()
    : code_typet()
  {
    return_type()=bool_typet();
  }
};

class predicate_symbol_exprt : public symbol_exprt 
{
public:
  explicit predicate_symbol_exprt(
    const irep_idt &identifier,
    const predicate_typet &type
    )
    : symbol_exprt(identifier, type)
  {
  }
};

typedef std::set<predicate_symbol_exprt> predicate_symbol_sett;


extern inline const predicate_symbol_exprt &to_predicate_symbol_expr(const exprt &expr)
{
  assert(expr.id()==ID_symbol && expr.operands().size()==1);
  return static_cast<const predicate_symbol_exprt &>(expr);
}

extern inline predicate_symbol_exprt &to_predicate_symbol_expr(exprt &expr)
{
  assert(expr.id()==ID_symbol && expr.operands().size()==1);
  return static_cast<predicate_symbol_exprt &>(expr);
}

class predicate_application_exprt : public exprt 
{
public:
  explicit predicate_application_exprt(
    const predicate_symbol_exprt &_predicate)
    : exprt(ID_function_application)
  {
    operands().resize(3);
    predicate()=_predicate;
    set(ID_guard,true_exprt());
  }

  explicit predicate_application_exprt(
    const predicate_symbol_exprt &_predicate,
    const exprt &_guard)
    : exprt(ID_function_application)
  {
    operands().resize(3);
    predicate()=_predicate;
    set(ID_guard,_guard);
  }

  predicate_symbol_exprt &predicate()
  {
    return to_predicate_symbol_expr(op0());
  }

  const predicate_symbol_exprt &predicate() const
  {
    return to_predicate_symbol_expr(op0());
  }

  typedef exprt::operandst argumentst;

  argumentst &arguments()
  {
    return op1().operands();
  }

  const argumentst &arguments() const
  {
    return op1().operands();
  }

  const exprt &guard() const
  {
    return static_cast<const exprt &>(find(ID_guard));
  }
};

extern inline const predicate_application_exprt &to_predicate_application_expr(const exprt &expr)
{
  assert(expr.id()==ID_function_application && expr.operands().size()==2);
  return static_cast<const predicate_application_exprt &>(expr);
}

extern inline predicate_application_exprt &to_predicate_application_expr(exprt &expr)
{
  assert(expr.id()==ID_function_application && expr.operands().size()==2);
  return static_cast<predicate_application_exprt &>(expr);
}

#endif
