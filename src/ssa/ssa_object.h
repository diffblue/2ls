/*******************************************************************\

Module: SSA Objects

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_SSA_OBJECTS_H
#define CPROVER_SSA_OBJECTS_H

#include <goto-programs/goto_functions.h>

class ssa_objectt
{
public:
  inline explicit ssa_objectt(const exprt &_expr, const namespacet &_ns):
    expr(_expr),
    identifier(object_id_rec(expr, _ns))
  {
  }
  
  inline const exprt &get_expr() const
  {
    return expr;
  }
  
  inline irep_idt get_identifier() const
  {
    return identifier;
  }
  
  // The identifier is unique, so ordering and comparison
  // can be done on the identifier.
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
    return identifier.empty()?0:(void *)&identifier;
  }
  
  exprt get_root_object() const
  {
    return get_root_object_rec(expr);
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
  objectst objects, dirty_locals, clean_locals, globals;
  
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

// Returns true if the member expression is a struct member
// expression.
bool is_struct_member(const member_exprt &, const namespacet &);

// Returns true for symbol(.member)*, where
// all members are struct members.
bool is_symbol_struct_member(const exprt &, const namespacet &);

// Returns true for ((*ptr)|symbol)(.member)*, where
// all members are struct members.
bool is_symbol_or_deref_struct_member(const exprt &, const namespacet &);

// Returns true for (*ptr)(.member)*, where
// all members are struct members.
bool is_deref_struct_member(const exprt &, const namespacet &);

#endif
