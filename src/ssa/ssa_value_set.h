/*******************************************************************\

Module: A flow-insensitive value set analysis

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// A flow-insensitive value set analysis

#ifndef CPROVER_2LS_SSA_SSA_VALUE_SET_H
#define CPROVER_2LS_SSA_SSA_VALUE_SET_H

#include <analyses/ai.h>
#include <util/options.h>
#include <util/threeval.h>

#include "ssa_object.h"

class ssa_value_domaint:public ai_domain_baset
{
public:
  ssa_value_domaint(): has_values(false) {}

  void transform(
    const irep_idt &,
    locationt,
    const irep_idt &,
    locationt,
    ai_baset &,
    const namespacet &) override;
  void output(
    std::ostream &,
    const ai_baset &,
    const namespacet &) const override;
  bool merge(const ssa_value_domaint &, locationt, locationt);

  void make_bottom() override
  {
    value_map.clear();
    has_values=tvt(false);
  }

  void make_top() override
  {
    value_map.clear();
    has_values=tvt(true);
  }

  void make_entry() override
  {
    make_top();
  }

  bool is_bottom() const override
  {
    return has_values.is_false();
  }

  bool is_top() const override
  {
    return has_values.is_true();
  }

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

  bool competition_mode=false;

  const valuest operator()(
    const exprt &src,
    const namespacet &ns) const
  {
    valuest tmp;
    assign_rhs_rec(tmp, src, ns, false, 0);
    return tmp;
  }

protected:
  tvt has_values;

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
    const irep_idt &function_identifier,
    const goto_functionst::goto_functiont &goto_function,
    const namespacet &ns_,
    const optionst &_options):
    ns(ns_),
    options(_options)
  {
    operator()(function_identifier, goto_function, ns_);
  }

protected:
  void initialize(
    const irep_idt &function_id,
    const goto_functionst::goto_functiont &goto_function) override;

  void assign_ptr_param(const exprt &expr, ssa_value_domaint &entry);

  void assign(const exprt &src, const exprt &dest, ssa_value_domaint &entry);

  const namespacet &ns;
  const optionst &options;

  friend class ssa_value_domaint;
};

#endif
