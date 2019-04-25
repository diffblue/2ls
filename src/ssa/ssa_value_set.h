/*******************************************************************\

Module: A flow-insensitive value set analysis

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// A flow-insensitive value set analysis

#ifndef CPROVER_2LS_SSA_SSA_VALUE_SET_H
#define CPROVER_2LS_SSA_SSA_VALUE_SET_H

#include <analyses/ai.h>

#include "ssa_object.h"
#include "ssa_heap_domain.h"

class ssa_value_domaint:public ai_domain_baset
{
public:
  virtual void transform(locationt, locationt, ai_baset &, const namespacet &);
  virtual void output(
    std::ostream &,
    const ai_baset &,
    const namespacet &) const;
  bool merge(const ssa_value_domaint &, locationt, locationt);

  struct valuest
  {
  public:
    typedef std::set<ssa_objectt> value_sett;
    value_sett value_set;
    bool offset, null, unknown, integer_address;
    unsigned alignment;

    inline valuest():
      offset(false),
      null(false),
      unknown(false),
      integer_address(false),
      alignment(0)
    {
    }

    void output(std::ostream &, const namespacet &) const;

    bool merge(
      const valuest &src,
      bool is_loop_back=false,
      const irep_idt &object_id=irep_idt());

    inline void clear()
    {
      *this=valuest();
    }

    inline bool empty() const
    {
      return value_set.empty() && !null && !unknown && !integer_address;
    }
  };

  // maps objects to values
  typedef std::map<ssa_objectt, valuest> value_mapt;
  value_mapt value_map;

  const valuest operator()(const exprt &src, const namespacet &ns) const
  {
    valuest tmp;
    assign_rhs_rec(tmp, src, ns, false, 0);
    return tmp;
  }

protected:
  void assign_lhs_rec(
    const exprt &lhs,
    const exprt &rhs,
    const namespacet &,
    bool add=false);

  void assign_rhs_rec(
    valuest &lhs,
    const exprt &rhs,
    const namespacet &,
    bool offset,
    unsigned alignment) const;

  void assign_rhs_rec_address_of(
    valuest &lhs,
    const exprt &rhs,
    const namespacet &,
    bool offset,
    unsigned alignment) const;

  void assign_pointed_rhs_rec(const exprt &rhs, const namespacet &ns);

  static unsigned merge_alignment(unsigned a, unsigned b)
  {
    // could use lcm here
    if(a==b)
      return a;
    if(a==0)
      return b;
    if(b==0)
      return a;
    return 1;
  }
};

class ssa_value_ait:public ait<ssa_value_domaint>
{
public:
  ssa_value_ait(
    const goto_functionst::goto_functiont &goto_function,
    const namespacet &ns_,
    const ssa_heap_analysist &_heap_analysis):
    ns(ns_),
    heap_analysis(_heap_analysis)
  {
    operator()(goto_function, ns_);
  }

protected:
  virtual void initialize(
    const goto_functionst::goto_functiont &goto_function) override;

  void assign_ptr_param(const exprt &expr, ssa_value_domaint &entry);

  void assign(const exprt &src, const exprt &dest, ssa_value_domaint &entry);

  const namespacet &ns;

  const ssa_heap_analysist &heap_analysis;

  friend class ssa_value_domaint;
};

#endif
