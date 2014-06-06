/*******************************************************************\

Module: Abstract Interface for a Function Summary

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_SUMMARIZER_FUNCTION_SUMMARY_H
#define CPROVER_SUMMARIZER_FUNCTION_SUMMARY_H

#include <set>

#include <util/expr.h>

class function_summaryt
{
public:
  virtual ~function_summaryt()
  {
  }

  typedef std::set<exprt> modifiest;

  // get set of objects modified
  virtual const modifiest &get_modifies() const;
  
  // get transition relation
  virtual exprt as_expr() const;
};

#endif
