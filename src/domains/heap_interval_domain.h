/**
 *  Viktor Malik, 3/30/17 (c).
 */
#ifndef INC_2LS_HEAP_INTERVAL_DOMAINT_H
#define INC_2LS_HEAP_INTERVAL_DOMAINT_H


#include "domain.h"
#include "tpolyhedra_domain.h"
#include "heap_domain.h"

class heap_interval_domaint : public domaint
{
 public:
  heap_domaint heap_domain;
  tpolyhedra_domaint interval_domain;

  heap_domaint::heap_valuet heap_value;

  heap_interval_domaint(
    unsigned int _domain_number,
    replace_mapt &_renaming_map,
    const var_specst &var_specs,
    const namespacet &ns):
    domaint(_domain_number, _renaming_map, ns),
    heap_domain(_domain_number, _renaming_map, var_specs, ns),
    interval_domain(_domain_number, _renaming_map, ns)
  {
    interval_domain.add_interval_template(var_specs, ns);
  }

  class heap_interval_valuet:public valuet
  {
   public:
    heap_domaint::heap_valuet heap_value;
    tpolyhedra_domaint::templ_valuet interval_value;
  };

  virtual void initialize(valuet &value) override;

  virtual void output_value(
    std::ostream &out,
    const valuet &value,
    const namespacet &ns) const override;

  virtual void output_domain(
    std::ostream &out, const namespacet &ns) const override;

  virtual void project_on_vars(valuet &value, const var_sett &vars, exprt &result) override;
};


#endif //INC_2LS_HEAP_INTERVAL_DOMAINT_H
