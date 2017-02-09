/**
 *  Viktor Malik, 12.8.2016 (c).
 */

//#define DEBUG_OUTPUT

#include "strategy_solver_heap.h"

bool strategy_solver_heapt::iterate(invariantt &_inv)
{
  heap_domaint::heap_valuet &inv=
    static_cast<heap_domaint::heap_valuet &>(_inv);

  bool improved = false;

  solver.new_context();

  // Entry value constraints
  exprt pre_expr = heap_domain.to_pre_constraints(inv);
#ifdef DEBUG_OUTPUT
  debug() << "pre-inv: " << from_expr(ns, "", pre_expr) << eom;
#endif
  solver << pre_expr;

  // Exit value constraints
  exprt::operandst strategy_cond_exprs;
  heap_domain.make_not_post_constraints(
    inv, strategy_cond_exprs, strategy_value_exprs);

  strategy_cond_literals.resize(strategy_cond_exprs.size());

#ifdef DEBUG_OUTPUT
  debug() << "post-inv: ";
#endif
  for (unsigned i = 0; i < strategy_cond_exprs.size(); ++i)
  {
#ifdef DEBUG_OUTPUT
    debug() << (i > 0 ? " || " : "")
            << from_expr(ns, "", strategy_cond_exprs[i]);
#endif
    strategy_cond_literals[i] = solver.convert(strategy_cond_exprs[i]);
    strategy_cond_exprs[i] = literal_exprt(strategy_cond_literals[i]);
  }
#ifdef DEBUG_OUTPUT
  debug() << eom;
#endif
  solver << disjunction(strategy_cond_exprs);

#ifdef DEBUG_OUTPUT
  debug() << "solve(): ";
#endif

  if (solver() == decision_proceduret::D_SATISFIABLE)  // improvement check
  {
#ifdef DEBUG_OUTPUT
    debug() << "SAT" << eom;
#endif

#ifdef DEBUG_OUTPUT
    for (unsigned i = 0; i < solver.activation_literals.size(); i++)
    {
      debug() << "literal: " << solver.activation_literals[i] << " " <<
              solver.l_get(solver.activation_literals[i]) << eom;
    }
    for (unsigned i = 0; i < solver.formula.size(); i++)
    {
      debug() << "literal: " << solver.formula[i] << " " <<
              solver.l_get(solver.formula[i]) << eom;
    }
    for (unsigned i = 0; i < heap_domain.templ.size(); i++)
    {
      exprt c = heap_domain.get_row_pre_constraint(i, inv[i]);
      debug() << "cond: " << from_expr(ns, "", c) << " " <<
              from_expr(ns, "", solver.get(c)) << eom;
      debug() << "guards: "
              << from_expr(ns, "", heap_domain.templ[i].pre_guard)
              << " "
              << from_expr(ns, "", solver.get(heap_domain.templ[i].pre_guard))
              << eom;
      debug() << "guards: "
              << from_expr(ns, "", heap_domain.templ[i].post_guard) << " "
              << from_expr(ns, "", solver.get(heap_domain.templ[i].post_guard))
              << eom;
      exprt post = heap_domain.get_row_post_constraint(i, inv[i]);
      debug() << "post-cond: " << from_expr(ns, "", post) << " "
              << from_expr(ns, "", solver.get(post)) << eom;
      print_solver_expr(c);
      print_solver_expr(post);
    }
#endif

    for (unsigned row = 0; row < strategy_cond_literals.size(); ++row)
    {
      if (solver.l_get(strategy_cond_literals[row]).is_true())
      {
        debug() << "updating row: " << row << eom;

        const heap_domaint::template_rowt &templ_row = heap_domain.templ[row];

        int actual_loc = heap_domain.get_symbol_loc(templ_row.expr);

        exprt pointer = strategy_value_exprs[row];
        exprt value = solver.get(pointer);
        // Value from solver must be converted into expression
        exprt ptr_value = heap_domain.value_to_ptr_exprt(value);

        if ((ptr_value.id() == ID_constant &&
             to_constant_expr(ptr_value).get_value() == ID_NULL) ||
            ptr_value.id() == ID_symbol)
        {
          // Add equality p == NULL or p == symbol
          if (heap_domain.add_points_to(row, inv, ptr_value))
          {
            improved = true;
            debug() << "Add "
                    << (templ_row.mem_kind == heap_domaint::STACK ?
                        "points to " : "path to ")
                    << from_expr(ns, "", ptr_value) << eom;
          }
        }
        else if (ptr_value.id() == ID_address_of)
        {
          // pointer points to the heap (p = &obj)
          debug() << from_expr(ns, "", ptr_value) << eom;
          assert(ptr_value.id() == ID_address_of);
          // Canonize address
          assert(to_address_of_expr(ptr_value).object().id() == ID_symbol);

          symbol_exprt obj=to_symbol_expr(to_address_of_expr(ptr_value).object());

          // Add equality p == &obj
          if (heap_domain.add_points_to(row, inv, obj))
          {
            improved = true;
            debug() << "Add "
                    << (templ_row.mem_kind == heap_domaint::STACK ?
                        "points to " : "path to ")
                    << from_expr(ns, "", obj) << eom;
          }

          if(templ_row.mem_kind==heap_domaint::HEAP &&
             obj.type().get_bool("#dynamic") &&
             id2string(obj.get_identifier()).find("$unknown")==
             std::string::npos)
          {
            // Find row with corresponding member field
            // of pointed object (obj.member)
            int member_val_index;
            member_val_index=find_member_row(
              obj, templ_row.member, actual_loc, templ_row.kind);
            assert(member_val_index>=0);

            // Add all paths from obj.next to p
            if(heap_domain.add_transitivity(
                 row, (unsigned) member_val_index, inv))
            {
              improved = true;
              debug()
                << "Add all paths: "
                << from_expr(ns, "", heap_domain.templ[member_val_index].expr)
                << ", through: " << from_expr(ns, "", obj) << eom;
            }
          }
        }
        else
        {
          if (heap_domain.set_nondet(row, inv))
          {
            improved = true;
            debug() << "Set nondet" << eom;
          }
        }

        if (templ_row.mem_kind == heap_domaint::HEAP)
        { // Recursively update all rows that are dependent on this row
          updated_rows.clear();
          update_rows_rec(row, inv);
        }
      }
    }
  }

  else
  {
    debug() << "UNSAT" << eom;

#ifdef DEBUG_OUTPUT
    for (unsigned i = 0; i < solver.formula.size(); i++)
    {
      if (solver.solver->is_in_conflict(solver.formula[i]))
        debug() << "is_in_conflict: " << solver.formula[i] << eom;
      else
        debug() << "not_in_conflict: " << solver.formula[i] << eom;
    }

    for (unsigned i = 0; i < heap_domain.templ.size(); i++)
    {
      exprt c = heap_domain.get_row_pre_constraint(i, inv[i]);
      debug() << "cond: " << from_expr(ns, "", c) << " " <<
              from_expr(ns, "", solver.get(c)) << eom;
      debug() << "guards: "
              << from_expr(ns, "", heap_domain.templ[i].pre_guard)
              << " "
              << from_expr(ns, "", solver.get(heap_domain.templ[i].pre_guard))
              << eom;
      debug() << "guards: "
              << from_expr(ns, "", heap_domain.templ[i].post_guard) << " "
              << from_expr(ns, "", solver.get(heap_domain.templ[i].post_guard))
              << eom;
      exprt post = heap_domain.get_row_post_constraint(i, inv[i]);
      debug() << "post-cond: " << from_expr(ns, "", post) << " "
              << from_expr(ns, "", solver.get(post)) << eom;
    }
#endif
  }
  solver.pop_context();

  return improved;
}

/**
 * Find the template row that contains specified member field 
 * of a dynamic object at given location.
 * Finds obj.member#loc with maximal loc less than actual_loc.
 * @param obj
 * @param member Member field to find
 * @param actual_loc Actual location number
 * @return Template row of obj.member
 */
int strategy_solver_heapt::find_member_row(
  const exprt &obj,
  const irep_idt &member,
  int actual_loc,
  const domaint::kindt &kind)
{
  assert(obj.id() == ID_symbol);
  std::string obj_id = heap_domain.get_base_name(obj);

  int result = -1;
  int max_loc = -1;
  for (unsigned i = 0; i < heap_domain.templ.size(); ++i)
  {
    heap_domaint::template_rowt &templ_row = heap_domain.templ[i];
    if (templ_row.kind == kind && templ_row.member == member &&
        templ_row.mem_kind == heap_domaint::HEAP)
    {
      std::string id=id2string(to_symbol_expr(templ_row.expr).get_identifier());
      if (id.find(obj_id) != std::string::npos)
      {
        int loc = heap_domain.get_symbol_loc(templ_row.expr);
        if (loc > max_loc && (kind == domaint::OUT || loc <= actual_loc))
        {
          max_loc = loc;
          result = i;
        }
      }
    }
  }
  return result;
}

/**
 * Recursively update rows that point to given row.
 * @param row Pointed row
 * @param value Heap value
 * @return True if any change occured
 */
bool strategy_solver_heapt::update_rows_rec(
  const heap_domaint::rowt &row,
  heap_domaint::heap_valuet &value)
{
  heap_domaint::heap_row_valuet &row_value =
      static_cast<heap_domaint::heap_row_valuet &>(value[row]);
  const heap_domaint::template_rowt &templ_row = heap_domain.templ[row];

  updated_rows.insert(row);
  bool result = false;
  for (auto &ptr : row_value.pointed_by)
  {
    if (heap_domain.add_transitivity(ptr, row, value))
      result = true;
    debug() << "recursively updating row: " << ptr << eom;
    debug() << "add all paths: " << from_expr(ns, "", templ_row.expr)
            << ", through: "
            << from_expr(ns, "", templ_row.dyn_obj) << eom;
    // Recursive update is called for each row only once
    if (updated_rows.find(ptr) == updated_rows.end())
      result = update_rows_rec(ptr, value) || result;
  }
  return result;
}

void strategy_solver_heapt::print_solver_expr(const exprt &expr)
{
  debug() << from_expr(ns, "", expr) << ": "
          << from_expr(ns, "", solver.get(expr)) << eom;
  forall_operands(it, expr)
      print_solver_expr(*it);
}

void strategy_solver_heapt::initialize(
  const local_SSAt &SSA,
  const exprt &precondition,
  template_generator_baset &template_generator)
{
  // Bind list advancers
  bind_advancers(SSA, precondition, template_generator);

  // Create preconditions for input variables if not exist
  exprt::operandst equs;
  for (auto &param : SSA.params)
    create_precondition(param, precondition, equs);
  for (auto &global_in : SSA.globals_in)
    create_precondition(global_in, precondition, equs);
  if (!equs.empty())
    solver << conjunction(equs);
}

/*******************************************************************\

Function: strategy_solver_heapt::collect_preconditions_rec

  Inputs: Expression and calling context (precondition)

 Outputs: Set of preconditions corresponding to given expression.

 Purpose: Recursively find all preconditions for the given expression
          in the calling context.
          Returns right-hand sides of equalities where expr is left-hand
          side.

\*******************************************************************/

std::set<exprt> strategy_solver_heapt::collect_preconditions_rec(
  const exprt &expr,
  const exprt &precondition)
{
  std::set<exprt> result;
  if (precondition.id() == ID_equal)
  {
    const equal_exprt &eq = to_equal_expr(precondition);
    if (eq.lhs() == expr && eq.rhs() != expr)
    {
      result.insert(eq.rhs());
    }
  }
  else
  {
    forall_operands(it, precondition)
      {
        std::set<exprt> op_result = collect_preconditions_rec(expr, *it);
        result.insert(op_result.begin(), op_result.end());
      }
  }
  return result;
}

/*******************************************************************\

Function: strategy_solver_heapt::create_precondition

  Inputs: Variable, calling context (precondition) and reference to
          bindings list.

 Outputs:

 Purpose: Create precondition for given variable at the input of the
          function if it does not exist in given calling context.

\*******************************************************************/

void strategy_solver_heapt::create_precondition(
  const symbol_exprt &var,
  const exprt &precondition,
  exprt::operandst &equs)
{
  if (var.type().id() == ID_pointer &&
      id2string(var.get_identifier()).find('.') == std::string::npos)
  {
    auto pre = collect_preconditions_rec(var, precondition);
    if (pre.empty())
    {
      debug() << "Creating precondition for pointer parameters" << eom;
      const symbolt *symbol;
      if (ns.lookup(id2string(var.get_identifier()), symbol)) return;

      address_of_exprt init_value(symbol->symbol_expr());
      init_value.type() = symbol->type;
      equs.push_back(equal_exprt(var, init_value));
    }
  }
}

/*******************************************************************\

Function: strategy_solver_heapt::collect_advancers

  Inputs: SSA

 Outputs:

 Purpose: Collect all advancers and their instances in the given SSA

\*******************************************************************/

void strategy_solver_heapt::collect_advancers(const local_SSAt &SSA)
{
  for (const symbol_exprt &global : SSA.globals_in)
  {
    if (global.type().id() == ID_pointer &&
        id2string(global.get_identifier()).find('.') != std::string::npos)
    { // Get all pointer-typed fields of input structure objects
      const typet &pointed_type = ns.follow(global.type().subtype());
      if (pointed_type.id() == ID_struct)
      {
        // Split pointer'obj.member into pointer and member
        const std::string id = id2string(global.get_identifier());
        const irep_idt member = id.substr(id.find_last_of('.') + 1);
        const irep_idt pointer_id = id.substr(0, id.rfind("'obj." + id2string(member)));
        // Find the corresponding pointer (must be in global objects or parameters)
        symbol_exprt pointer("");
        for (const symbol_exprt &param : SSA.params)
        {
          if (param.get_identifier() == pointer_id)
          {
            pointer = param;
            break;
          }
        }
        if (pointer.get_identifier() == "")
        {
          for (const symbol_exprt &global_other : SSA.globals_in)
          {
            if (global_other.get_identifier() == pointer_id)
            {
              pointer = global_other;
              break;
            }
          }
        }
        assert(pointer.get_identifier() != "");

        // Create advancer
        advancers.emplace_back(pointer, member);
        advancert &advancer = advancers.back();

        // Collect advancer instances
        for (auto &component : to_struct_type(pointed_type).components())
        {
          const irep_idt &component_name = component.get_name();
          // Read-access advancer instance
          advancer.add_instance(component_name, IN_LOC);

          // Find all write-accesses and create corresponding advancer instances
          ssa_objectt instance_obj(advancer.instance_symbol_expr(component_name, IN_LOC), SSA.ns);
          std::list<unsigned> written_locs = SSA.all_assignment_locs(instance_obj);
          for (unsigned loc : written_locs)
          {
            advancer.add_instance(component_name, loc);
          }
        }
      }
    }
  }
}

/*******************************************************************\

Function: strategy_solver_heapt::reachable_objects

  Inputs: List advancer, function call calling context represented by
          precondition.

 Outputs: Set of reachable objects

 Purpose: Find all objects reachable from advancer pointer via advancer
          field in the given precondition.

\*******************************************************************/

std::set<symbol_exprt> strategy_solver_heapt::reachable_objects(
  const advancert &advancer,
  const exprt &precondition)
{
  std::set<symbol_exprt> result;

  // Collect all addresses pointed by advancer pointer (from stack template rows of the
  // calling context)
  std::set<exprt> pointed_objs = collect_preconditions_rec(advancer.pointer, precondition);
  for (const exprt &pointed : pointed_objs)
  {
    if (pointed.id() == ID_address_of)
    {
      const exprt &pointed_obj = to_address_of_expr(pointed).object();
      assert(pointed_obj.id() == ID_symbol);

      // Create obj.member
      symbol_exprt obj_member = recursive_member_symbol(to_symbol_expr(pointed_obj),
                                                        advancer.member, IN_LOC);
      obj_member.type() = advancer.pointer.type();

      // Collect all reachable objects (from heap rows of the calling context)
      std::set<exprt> reachable_objs = collect_preconditions_rec(obj_member, precondition);
      for (const exprt &reachable : reachable_objs)
      {
        if (reachable.id() == ID_address_of)
        {
          const exprt &reachable_obj = to_address_of_expr(reachable).object();
          assert(reachable_obj.id() == ID_symbol);

          result.insert(to_symbol_expr(reachable_obj));
        }
      }
    }
  }

  return result;
}

/*******************************************************************\

Function: strategy_solver_heapt::bind_advancers

  Inputs: SSA, calling context represented by precondition and reference
          to template generator

 Outputs:

 Purpose: Bind advancers from SSA to actual heap objects from the
          calling context.

\*******************************************************************/

void strategy_solver_heapt::bind_advancers(
  const local_SSAt &SSA, const exprt &precondition,
  template_generator_baset &template_generator)
{
  collect_advancers(SSA);

  for (const advancert &advancer : advancers)
  {
    exprt::operandst reachable_bindings;

    std::set<symbol_exprt> reachable_objs = reachable_objects(advancer, precondition);

    exprt::operandst adv_bindings;
    for (const symbol_exprt &reachable : reachable_objs)
    {
      // Bind address of advancer (represented by symbol) with &(reachable)
      address_of_exprt reachable_addr = address_of_exprt(reachable);
      reachable_addr.object().type().set("#dynamic", true);
      adv_bindings.push_back(equal_exprt(
          symbol_exprt(id2string(advancer.symbol_expr().get_identifier()) + "'addr",
                       advancer.pointer.type()),
          reachable_addr));

      // Bind reachable.m with advancer instance
      for (auto &instance: advancer.instances)
      {
        for (const int &instance_loc : instance.second)
        {
          adv_bindings.push_back(equal_exprt(
              recursive_member_symbol(reachable, instance.first, instance_loc),
              advancer.instance_symbol_expr(instance.first, instance_loc)
          ));
        }
      }
      reachable_bindings.push_back(conjunction(adv_bindings));

      // Create new template rows for output write instances
      for (const std::pair<irep_idt, int> &instance : advancer.output_instances())
      {
        new_output_template_row(SSA,
                                recursive_member_symbol(reachable, instance.first, instance.second),
                                template_generator);
      }
    }

    if (!reachable_bindings.empty())
    {
      advancer_bindings = disjunction(reachable_bindings);
      debug() << "Advancers bindings:" << eom;
      debug() << from_expr(SSA.ns, "", advancer_bindings) << eom;
      solver << advancer_bindings;

      debug() << "Template after advancer binding:" << eom;
      heap_domain.output_domain(debug(), SSA.ns);
    }
  }
}

/*******************************************************************\

Function: strategy_solver_heapt::recursive_member_symbol

  Inputs: Structure-typed object, name of its member and a location number.

 Outputs: Corresponding symbol:
          object.member#loc, or object.memer if loc is input

 Purpose:

\*******************************************************************/

const symbol_exprt strategy_solver_heapt::recursive_member_symbol(
  const symbol_exprt &object,
  const irep_idt &member,
  const int loc_num)
{
  std::string suffix = loc_num != IN_LOC ? ("#" + std::to_string(loc_num)) : "";
  return symbol_exprt(id2string(object.get_identifier()) + "." + id2string(member) + suffix,
                      pointer_typet(object.type()));
}

/*******************************************************************\

Function: strategy_solver_heapt::new_output_template_row

  Inputs: SSA, new row variable and the template generator

 Outputs:

 Purpose: Insert new output template row into the template.

\*******************************************************************/

void strategy_solver_heapt::new_output_template_row(
  const local_SSAt &SSA,
  const symbol_exprt &var,
  template_generator_baset &template_generator)
{
  exprt guard = SSA.guard_symbol(--SSA.goto_function.body.instructions.end());

  template_generator.var_specs.push_back(domaint::var_spect());
  domaint::var_spect &var_spec = template_generator.var_specs.back();

  var_spec.var = var;
  var_spec.pre_guard = guard;
  var_spec.post_guard = guard;
  var_spec.aux_expr = true_exprt();
  var_spec.kind = domaint::OUT;

  assert(var.type().id() == ID_pointer);
  const typet &pointed_type = ns.follow(var.type().subtype());
  heap_domain.add_template_row(var_spec, pointed_type);
  heap_domain.new_heap_row_vars.push_back(var);
}
