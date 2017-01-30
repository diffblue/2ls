/**
 * Strategy solver for heap verification.
 *  Viktor Malik, 12.8.2016 (c).
 */
#ifndef CPROVER_STRATEGY_SOLVER_HEAP_H
#define CPROVER_STRATEGY_SOLVER_HEAP_H

#include "../ssa/local_ssa.h"
#include "strategy_solver_base.h"
#include "heap_domain.h"
#include "template_generator_base.h"

class strategy_solver_heapt : public strategy_solver_baset
{
 public:
  explicit strategy_solver_heapt(heap_domaint &_heap_domain, incremental_solvert &_solver,
                                 const local_SSAt &SSA, const exprt &precondition,
                                 message_handlert &message_handler,
                                 template_generator_baset &template_generator)
      : strategy_solver_baset(_solver, SSA.ns), heap_domain(_heap_domain)
  {
    set_message_handler(message_handler);
    initialize(SSA, precondition, template_generator);
  }

  virtual bool iterate(invariantt &_inv) override;

  void initialize(const local_SSAt &SSA, const exprt &precondition,
                  template_generator_baset &template_generator);

 protected:

  class advancert
  {
   public:
    symbol_exprt pointer;
    irep_idt member;

    std::map<irep_idt, std::set<int> > instances;

    advancert(const symbol_exprt &pointer_, const irep_idt &member_)
        : pointer(pointer_), member(member_) {}

    bool operator<(const advancert &rhs) const
    {
      return std::tie(pointer, member) < std::tie(rhs.pointer, rhs.member);
    }

    void add_instance(const irep_idt &member, const int location_number)
    {
      instances[member].insert(location_number);
    }

    const symbol_exprt symbol_expr() const
    {
      return symbol_exprt(
          id2string(pointer.get_identifier()) + "'obj." + id2string(member) + "'adv",
          pointer.type().subtype());
    }

    const symbol_exprt instance_symbol_expr(const irep_idt &member, const int location_number) const
    {
      return recursive_member_symbol(symbol_expr(), member, location_number);
    }

    const std::list<std::pair<irep_idt, int>> output_instances() const
    {
      std::list<std::pair<irep_idt, int>> result;

      // Find instance with maximal location number
      for (auto &instance : instances)
      {
        int max_loc = *(--(instance.second.end()));
        if (max_loc >= 0)
          result.emplace_back(instance.first, max_loc);
      }

      return result;
    }
  };

  static const int IN_LOC = -1;

  heap_domaint &heap_domain;
  std::set<unsigned> updated_rows;

  std::list<advancert> advancers;
  exprt advancer_bindings;

  int find_member_row(const exprt &obj, const irep_idt &member, int actual_loc,
                      const domaint::kindt &kind);

  bool update_rows_rec(const heap_domaint::rowt &row, heap_domaint::heap_valuet &value);

  void print_solver_expr(const exprt &expr);

  void create_precondition(const symbol_exprt &var,
                           const exprt &precondition,
                           exprt::operandst &equs);

  void bind_advancers(const local_SSAt &SSA, const exprt &precondition,
                      template_generator_baset &template_generator);

  void collect_advancers(const local_SSAt &SSA);

  void new_output_template_row(const local_SSAt &SSA, const symbol_exprt &var,
                               template_generator_baset &template_generator);

  static std::set<symbol_exprt> reachable_objects(const advancert &advancer,
                                                  const exprt &precondition);

  static std::set<exprt> collect_preconditions_rec(const exprt &expr, const exprt &precondition);

  static const symbol_exprt recursive_member_symbol(const symbol_exprt &object,
                                                    const irep_idt &member,
                                                    const int loc_num);
};


#endif //CPROVER_STRATEGY_SOLVER_HEAP_H
