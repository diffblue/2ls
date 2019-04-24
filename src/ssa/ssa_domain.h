/*******************************************************************\

Module: Definition Analysis

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Definition Analysis

#ifndef CPROVER_2LS_SSA_SSA_DOMAIN_H
#define CPROVER_2LS_SSA_SSA_DOMAIN_H

#include <analyses/ai.h>

#include "assignments.h"

class ssa_domaint:public ai_domain_baset
{
public:
  // sources for identifiers
  struct deft
  {
    deft():kind(ASSIGNMENT) { }
    typedef enum { INPUT, ASSIGNMENT, PHI, ALLOCATION } kindt;
    kindt kind;
    locationt loc;
    exprt guard=nil_exprt();

    inline bool is_input() const { return kind==INPUT; }
    inline bool is_assignment() const { return kind==ASSIGNMENT; }
    inline bool is_phi() const { return kind==PHI; }
  };

  friend inline bool operator==(const deft &a, const deft &b)
  {
    return a.kind==b.kind && a.loc==b.loc;
  }

  friend inline std::ostream & operator << (
    std::ostream &out, const deft &d)
  {
    switch(d.kind)
    {
    case deft::INPUT: out << "INPUT"; break;
    case deft::ASSIGNMENT: out << d.loc->location_number; break;
    case deft::PHI: out << "PHI" << d.loc->location_number; break;
    case deft::ALLOCATION: out << "ALLOC" << d.loc->location_number; break;
    }
    return out;
  }

  // definition and source for an identifier
  struct def_entryt
  {
    def_entryt() { }
    deft def;
    locationt source; // information from?
  };

  friend inline std::ostream & operator << (
    std::ostream &out, const def_entryt &d)
  {
    return out << d.def << " from " << d.source->location_number;
  }

  typedef std::map<irep_idt, def_entryt> def_mapt;
  def_mapt def_map;

  // The phi nodes map identifiers to incoming branches:
  // map from source to definition.
  typedef std::map<unsigned, deft> loc_def_mapt;
  typedef std::map<irep_idt, loc_def_mapt> phi_nodest;
  phi_nodest phi_nodes;

  virtual void transform(
    locationt from,
    locationt to,
    ai_baset &ai,
    const namespacet &ns);

  virtual void output(
    std::ostream &out,
    const ai_baset &ai,
    const namespacet &ns) const;

  bool merge(
    const ssa_domaint &b,
    locationt from,
    locationt to);

private:
  static std::map<dstring, ssa_domaint::def_entryt>::const_iterator
  get_object_allocation_def(
    const irep_idt &id,
    const def_mapt &def_map);
};

class ssa_ait:public ait<ssa_domaint>
{
public:
  explicit ssa_ait(const assignmentst &_assignments):
    assignments(_assignments)
  {
  }

protected:
  const assignmentst &assignments;

  friend class ssa_domaint;

  // The overload below is needed to make the entry point get a source
  // for all objects.
  virtual void initialize(const goto_functionst::goto_functiont &goto_function);
};

#endif
