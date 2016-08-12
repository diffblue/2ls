/**
 *  Viktor Malik, 12.8.2016 (c).
 */
#ifndef CPROVER_HEAP_DOMAIN_H
#define CPROVER_HEAP_DOMAIN_H

#include "domain.h"

class heap_domaint : public domaint
{
 public:

  class pathst
  {
   public:
    inline void insert_path(vart _from, vart _to, member_exprt _field)
    {
      paths.push_back(patht());
      patht path = paths.back();
      path.from = _from;
      path.to = _to;
      path.field = _field;
    }

    inline void clear() { paths.clear(); }

    struct patht
    {
      vart from;
      vart to;
      member_exprt field;
    };
   protected:
    std::list<patht> paths;
  };

  typedef std::set<unsigned> index_sett;

  heap_domaint(unsigned int _domain_number, replace_mapt &_renaming_map,
               const var_specst &var_specs,
               const namespacet &ns)
      : domaint(_domain_number, _renaming_map)
  {
    make_template(var_specs, ns);
  }

  class heap_valuet : public valuet
  {
   public:
    pathst paths;
    index_sett nulls;
  };

  struct template_rowt
  {
    guardt pre_guard;
    guardt post_guard;
    exprt expr;
    exprt aux_expr;
    kindt kind;
  };

  typedef std::vector<template_rowt> templatet;

  virtual void initialize(valuet &value) override;

  exprt get_pre_null_constraint(unsigned index);

  exprt get_post_not_null_constraint(unsigned index);

  virtual void output_value(std::ostream &out, const valuet &value,
                            const namespacet &ns) const override;

  virtual void output_domain(std::ostream &out, const namespacet &ns) const override;

  virtual void project_on_vars(valuet &value, const var_sett &vars, exprt &result) override;

  void set_null(unsigned index, heap_valuet &value);

  void get_index_set(std::set<unsigned> &indices);

 protected:
  templatet templ;

  void make_template(const var_specst &var_specs, const namespacet &ns);
};


#endif //CPROVER_HEAP_DOMAIN_H
