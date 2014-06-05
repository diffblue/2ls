/*******************************************************************\

Module: SSA Objects

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_SSA_OBJECTS_H
#define CPROVER_SSA_OBJECTS_H

#include <goto-programs/goto_program.h>

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
  
  // this is for use in if(...) tests
  operator void *() const
  {
    return identifier.empty()?0:(void *)&identifier;
  }

protected:
  exprt expr;
  irep_idt identifier;

  static irep_idt object_id_rec(const exprt &src, const namespacet &);
};

class ssa_objectst
{
public:
  // objects, plus categorization
  typedef std::set<ssa_objectt> objectst;
  objectst objects, dirty_locals, clean_locals, globals;

  ssa_objectst(
    const goto_programt &goto_program,
    const namespacet &ns)
  {
    collect_objects(goto_program, ns);
    categorize_objects(ns);
  }
  
protected:
  void collect_objects(
    const goto_programt &,
    const namespacet &);

  void categorize_objects(const namespacet &);
};


#endif
