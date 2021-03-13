/*******************************************************************\

Module: SSA Objects

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// SSA Objects

#ifndef CPROVER_2LS_SSA_SSA_OBJECT_H
#define CPROVER_2LS_SSA_SSA_OBJECT_H

#include "ssa_pointed_objects.h"
#include <goto-programs/goto_functions.h>

class ssa_objectt
{
public:
  inline explicit ssa_objectt(const exprt &_expr, const namespacet &_ns):
    expr(_expr),
    identifier(object_id_rec(expr, _ns))
  {
  }

  inline const typet &type() const
  {
    return expr.type();
  }

  inline const exprt &get_expr() const
  {
    return expr;
  }

  inline irep_idt get_identifier() const
  {
    return identifier;
  }

  inline const symbol_exprt symbol_expr() const
  {
    return symbol_exprt(identifier, type());
  }

  // The identifier is unique, so ordering and comparison
  // can be done on the identifier, which in turn is
  // an integer.
  inline bool operator<(const ssa_objectt &other) const
  {
    return identifier<other.identifier;
  }

  inline bool operator==(const ssa_objectt &other) const
  {
    return identifier==other.identifier;
  }

  inline bool operator!=(const ssa_objectt &other) const
  {
    return identifier!=other.identifier;
  }

  // This is for use in if(...) tests, and
  // implements the 'safe bool' idiom. Shall be replaced
  // by C++11 explict conversion to bool one day.
  operator void *() const
  {
    return identifier.empty()?0:(void *)&identifier; // NOLINT(*)
  }

  exprt get_root_object() const
  {
    return get_root_object_rec(expr);
  }

  bool is_unknown_obj()
  {
    std::string id_str=id2string(identifier);
    return id_str.find("$unknown")!=std::string::npos;
  }

  void set_flag(const irep_idt flag, bool value)
  {
    expr.set(flag, value);
  }

protected:
  exprt expr;
  irep_idt identifier;

  static irep_idt object_id_rec(const exprt &src, const namespacet &);
  static exprt get_root_object_rec(const exprt &);
};

class ssa_objectst
{
public:
  // objects, plus categorization
  typedef std::set<ssa_objectt> objectst;
  objectst objects, dirty_locals, clean_locals, globals, ptr_objects;

  // literals whose address is taken
  typedef std::set<exprt> literalst;
  literalst literals;

  ssa_objectst(
    const goto_functionst::goto_functiont &goto_function,
    const namespacet &ns)
  {
    collect_objects(goto_function, ns);
    categorize_objects(goto_function, ns);
  }

protected:
  void collect_objects(
    const goto_functionst::goto_functiont &,
    const namespacet &);

  void categorize_objects(
    const goto_functionst::goto_functiont &,
    const namespacet &);
};

bool is_ptr_object(const exprt &);

// Returns true if the member expression is a struct member
// expression.
bool is_struct_member(const member_exprt &, const namespacet &);

// Returns true for symbol(.member)*, where
// all members are struct members.
bool is_symbol_struct_member(const exprt &, const namespacet &);

#endif
