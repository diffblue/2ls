/*******************************************************************\

Module: Dynamically allocated objects

Author: Viktor Malik

\*******************************************************************/

#ifndef CPROVER_2LS_DYNAMIC_OBJECTS_H
#define CPROVER_2LS_DYNAMIC_OBJECTS_H

#include "dynobj_instance_analysis.h"

#include <goto-programs/goto_model.h>
#include <goto-programs/goto_program.h>
#include <util/options.h>
#include <util/type.h>
#include <util/std_expr.h>
#include <util/symbol.h>

#include <string>
#include <vector>

class dynamic_objectt
{
public:
  dynamic_objectt(
    const goto_programt::instructiont *loc,
    const typet &type,
    const std::string &suffix,
    bool concrete);

  const typet &type() const { return symbol.type; }
  symbol_exprt symbol_expr() const { return symbol.symbol_expr(); }
  exprt address_of(const typet &result_type) const;
  const symbolt &get_symbol() const { return symbol; }

  bool operator==(const dynamic_objectt &rhs) const
  {
    return symbol.name==rhs.symbol.name;
  };

  void set_alloc_guard(const exprt &guard) { alloc_guard=guard; }
  const exprt &get_alloc_guard() const { return alloc_guard; }

private:
  symbolt symbol;
  const goto_programt::instructiont *loc;
  bool concrete;

  exprt alloc_guard=true_exprt();

  friend class dynamic_objectst;
};

class dynamic_objectst
{
public:
  dynamic_objectst(goto_modelt &goto_model):
    goto_model(goto_model), ns(goto_model.symbol_table) {}

  bool have_objects() const { return !db.empty(); }
  bool have_objects(const goto_programt::instructiont &loc) const
  {
    return db.find(&loc)!=db.end();
  }

  void clear() { db.clear(); }
  void clear(const goto_programt::instructiont &loc);

  const std::vector<dynamic_objectt> &get_objects(
    const goto_programt::instructiont &loc) const;
  const dynamic_objectt *get_single_abstract_object(
    const goto_programt::instructiont &loc);
  const dynamic_objectt *get_object_by_name(const irep_idt &name) const;

  dynamic_objectt &create_dynamic_object(
    const goto_programt::instructiont &loc,
    const typet &type,
    const std::string &suffix="",
    bool concrete=false);

  void replace_malloc(bool with_concrete);
  void generate_instances(const optionst &options);

private:
  typedef std::map<symbol_exprt, size_t> instance_countst;

  void erase_obj(const dynamic_objectt &obj);

  symbol_exprt create_object_select(
    const goto_programt::instructiont &loc,
    const std::string &suffix);

  bool get_malloc_size(
    const goto_programt::instructiont &loc,
    const goto_functionst::goto_functiont &current_function);
  typet get_object_type();
  exprt get_concrete_object_guard(
    const goto_programt::instructiont &loc,
    const dynamic_objectt &concrete_object);

  void replace_malloc_rec(
    exprt &malloc_expr,
    const goto_programt::instructiont &loc,
    bool with_concrete);

  instance_countst compute_instance_numbers(
    const goto_programt &goto_program,
    const dynobj_instance_analysist &analysis);
  exprt split_object(
    const dynamic_objectt *object, unsigned cnt, const typet &result_type);
  static void replace_object(
    const symbol_exprt &object,
    const exprt &new_expr,
    exprt &expr);

  std::map<const goto_programt::instructiont *,
           std::vector<dynamic_objectt>> db;

  // These are "state" variables used when parsing goto program
  goto_programt::instructiont *loop_end=nullptr;
  exprt malloc_size=nil_exprt();

  goto_modelt &goto_model;
  const namespacet ns;
};

int get_dynobj_line(const irep_idt &id);

#endif //CPROVER_2LS_DYNAMIC_OBJECTS_H