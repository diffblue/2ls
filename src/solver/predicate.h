/*******************************************************************\

Module: Predicate Expressions and Types

Author: Peter Schrammel

\*******************************************************************/

#ifndef CPROVER_2LS_PREDICATE_H
#define CPROVER_2LS_PREDICATE_H

#include <util/std_expr.h>
#include <util/std_expr.h>

class predicate_typet : public code_typet 
{
public:
  explicit predicate_typet()
    : code_exprt()
  {
    return_type()=bool_type();
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

class predicate_application_exprt : public exprt 
{
public:
  explicit predicate_application_exprt(
    const predicate_symbol_exprt &_predicate)
    : exprt(ID_function_application)
  {
    operands().resize(3);
    predicate()=_predicate;
    guard()=true_exprt();
  }

  explicit predicate_application_exprt(
    const predicate_symbol_exprt &_predicate,
    const exprt &_guard)
    : exprt(ID_function_application)
  {
    operands().resize(3);
    predicate()=_predicate;
    guard()=_guard;
  }

  exprt &predicate()
  {
    return op0();
  }

  const exprt &predicate() const
  {
    return op0();
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

  exprt &guard()
  {
    return op2();
  }

  const exprt &guard() const
  {
    return op2();
  }
};

extern inline const predicate_application_exprt &to_predicate_application_expr(const exprt &expr)
{
  assert(expr.id()==ID_function_application && expr.operands().size()==3);
  return static_cast<const predicate_application_exprt &>(expr);
}

extern inline predicate_application_exprt &to_predicate_application_expr(exprt &expr)
{
  assert(expr.id()==ID_predicate_application && expr.operands().size()==2);
  return static_cast<predicate_application_exprt &>(expr);
}

#endif
