/*******************************************************************\

Module: Dynamic objects analysis

Author: Viktor Malik

\*******************************************************************/

/// \file
/// Dynamic objects analysis

#include <algorithm>
#include "ssa_heap_domain.h"

void ssa_heap_domaint::transform(
  const namespacet &ns,
  domain_baset::locationt from,
  domain_baset::locationt to)
{
  if(from->is_assign())
  {
    const code_assignt &assign=to_code_assign(from->code);
    assign_lhs_rec(assign.lhs(), assign.rhs(), ns);
  }
  else if(from->is_function_call() && from->function==to->function)
  {
    const code_function_callt &fun_call=to_code_function_call(from->code);
    assert(fun_call.function().id()==ID_symbol);
    const irep_idt &fun_id=to_symbol_expr(fun_call.function()).get_identifier();

    if(function_map.find(fun_id)!=function_map.end())
    {
      unsigned counter=0;
      for(auto &obj : function_map.at(fun_id).new_objects)
      {
        symbol_exprt new_obj=obj.first;
        rename_to_caller(new_obj, from, counter);

        const symbolt *symbol;
        if(!ns.lookup(new_obj.get_identifier(), symbol))
          new_obj=symbol->symbol_expr();

        if(function_map[function].new_objects.find(new_obj)==
           function_map[function].new_objects.end())
        {
          function_map[function].new_objects.insert(
            std::make_pair(
              new_obj,
              std::set<exprt>()));
        }

        for(auto &expr : obj.second)
        {
          const exprt pointer=function_map.at(fun_id).corresponding_expr(
            expr, fun_call.arguments(), 0);

          objectst old_objects=value_map[pointer];
          value_map[pointer]={new_obj};

          if(is_function_output(pointer, function, ns, false))
          {
            function_map[function].new_objects.at(new_obj).insert(pointer);
          }

          for(auto &o : old_objects)
          {
            if(o.id()==ID_symbol && o.type().get_bool("#dynamic") &&
               new_obj!=o)
              function_map[function].new_objects.at(to_symbol_expr(o)).erase(
                pointer);
          }
        }
      }

      for(auto &obj : function_map.at(fun_id).modified_objects)
      {
        const exprt caller_obj=function_map.at(fun_id).corresponding_expr(
          obj, fun_call.arguments(), 0);
        if(is_function_output(caller_obj, function, ns, false))
          function_map[function].modified_objects.insert(caller_obj);
      }
    }
  }
}

bool ssa_heap_domaint::merge(
  const ssa_heap_domaint &other,
  domain_baset::locationt to)
{
  bool result=false;

  if(to->function=="" || to->function==other.function)
  {
    function=other.function;

    // Merge value maps - union
    for(auto &other_value : other.value_map)
    {
      if(value_map.find(other_value.first)==value_map.end())
      {
        value_map[other_value.first]=other_value.second;
        result=true;
      }
      else
      {
        unsigned long old_size=value_map[other_value.first].size();
        value_map[other_value.first].insert(
          other_value.second.begin(),
          other_value.second.end());
        result=old_size!=value_map[other_value.first].size();
      }
    }
  }
  else
  {
    function=to->function;
  }

  for(auto &f : other.function_map)
  {
    auto &objects=function_map[f.first].new_objects;
    const auto &other_objects=f.second.new_objects;

    if(f.first==function && function==other.function)
    {
      for(auto &other_object : other_objects)
      {
        if(objects.find(other_object.first)==objects.end())
        {
          objects[other_object.first]=other_object.second;
          result=true;
        }
        else if(!other_object.second.empty())
        {
          unsigned long old_size=objects[other_object.first].size();
          std::set<exprt> intersection;
          std::set_intersection(
            objects[other_object.first].begin(),
            objects[other_object.first].end(),
            other_object.second.begin(),
            other_object.second.end(),
            std::inserter(
              intersection,
              intersection.begin()));
          if(!intersection.empty())
            objects[other_object.first]=intersection;
          else
            objects.erase(other_object.first);

          if(old_size!=objects[other_object.first].size())
            result=true;
        }
      }
    }
    else
    {
      for(auto &o : other_objects)
      {
        std::size_t old_size=objects[o.first].size();
        objects[o.first]=o.second;
        if(old_size!=objects[o.first].size())
          result=true;
      }
    }

    function_map[f.first].params=f.second.params;

    std::size_t old_size=function_map[f.first].modified_objects.size();
    function_map[f.first].modified_objects.insert(
      f.second.modified_objects.begin(),
      f.second.modified_objects.end());
    if(old_size!=function_map[f.first].modified_objects.size())
      result=true;
  }

  return result;
}

void ssa_heap_domaint::assign_rhs(
  const exprt &rhs,
  const irep_idt &function,
  objectst &objects,
  const namespacet &ns)
{
  if(rhs.get_bool("#malloc_result"))
  {
    exprt malloc_result=rhs;
    if(malloc_result.id()==ID_typecast)
      malloc_result=to_typecast_expr(malloc_result).op();
    assert(malloc_result.id()==ID_address_of);

    const symbol_exprt new_object=to_symbol_expr(
      to_address_of_expr(malloc_result).object());

    function_infot &function_info=function_map[function];
    if(function_info.new_objects.find(new_object)==
       function_info.new_objects.end())
    {
      function_info.new_objects.insert(
        std::make_pair(
          new_object,
          std::set<exprt>()));
    }

    objects={new_object};
  }
  else if(rhs.id()==ID_typecast)
  {
    assign_rhs(to_typecast_expr(rhs).op(), function, objects, ns);
  }
  else
  {
    auto values=value_map.find(rhs);
    if(values!=value_map.end())
    {
      objects=values->second;
    }
  }
}

bool ssa_heap_domaint::is_function_output(
  const exprt &expr,
  const irep_idt &function,
  const namespacet &ns,
  bool in_deref)
{
  if(expr.id()==ID_dereference)
  {
    return is_function_output(
      to_dereference_expr(expr).pointer(),
      function,
      ns,
      true);
  }
  else if(expr.id()==ID_member)
  {
    return is_function_output(
      to_member_expr(expr).compound(),
      function,
      ns,
      in_deref);
  }
  else if(expr.id()==ID_symbol)
  {
    const symbol_exprt &symbol_expr=to_symbol_expr(expr);
    if(id2string(symbol_expr.get_identifier()).find("#return_value")!=
       std::string::npos)
    {
      return symbol_expr.get_identifier()==id2string(function)+"#return_value";
    }

    const symbolt *symbol;
    if(!ns.lookup(symbol_expr.get_identifier(), symbol) &&
       ((in_deref && symbol->is_parameter) || !symbol->is_procedure_local()))
      return true;
  }
  return false;
}

const std::set<symbol_exprt> ssa_heap_domaint::value(const exprt &expr) const
{
  std::set<symbol_exprt> result;
  if(value_map.find(expr)!=value_map.end())
  {
    for(auto &value : value_map.at(expr))
    {
      if(value.id()==ID_symbol)
        result.insert(to_symbol_expr(value));
    }
  }
  return result;
}

const std::list<symbol_exprt> ssa_heap_domaint::new_objects() const
{
  return new_objects(function);
}

const std::list<symbol_exprt> ssa_heap_domaint::new_objects(
  const irep_idt &fname) const
{
  std::list<symbol_exprt> result;
  if(function_map.find(fname)!=function_map.end())
  {
    for(auto &obj : function_map.at(fname).new_objects)
      result.push_back(obj.first);
  }
  return result;
}

void ssa_heap_domaint::rename_to_caller(
  symbol_exprt &object,
  domain_baset::locationt loc,
  unsigned &index) const
{
  object.set_identifier(
    "ssa::dynamic_object$"+std::to_string(loc->location_number)+"$"+
    std::to_string(index++));
}

const std::list<symbol_exprt> ssa_heap_domaint::new_caller_objects(
  const irep_idt &fname,
  domain_baset::locationt loc) const
{
  std::list<symbol_exprt> result=new_objects(fname);
  unsigned counter=0;
  for(symbol_exprt &o : result)
  {
    rename_to_caller(o, loc, counter);
  }
  return result;
}

const std::set<exprt> ssa_heap_domaint::modified_objects(
  const irep_idt &fname) const
{
  std::set<exprt> result;
  if(function_map.find(fname)!=function_map.end())
  {
    result=function_map.at(fname).modified_objects;
  }
  return result;
}

void ssa_heap_domaint::assign_lhs_rec(
  const exprt &lhs,
  const exprt &rhs,
  const namespacet &ns)
{
  objectst rhs_objects;
  assign_rhs(rhs, function, rhs_objects, ns);

  if(!rhs_objects.empty())
    value_map[lhs]=rhs_objects;
  else
    value_map.erase(lhs);

  if(is_function_output(lhs, function, ns, false))
  {
    auto &objects=function_map[function].new_objects;
    for(const exprt &o : rhs_objects)
    {
      if(o.id()==ID_symbol && o.type().get_bool("#dynamic"))
      {
        const symbol_exprt new_o=to_symbol_expr(o);
        if(objects.find(new_o)!=objects.end())
        {
          objects[new_o].insert(lhs);
        }
      }
    }
  }

  update_modified(lhs, ns);
}

void ssa_heap_domaint::update_modified(const exprt &expr, const namespacet &ns)
{
  if(expr.id()==ID_member)
  {
    update_modified(to_member_expr(expr).compound(), ns);
  }
  else if(expr.id()==ID_dereference)
  {
    for(const exprt &v : value_map[to_dereference_expr(expr).pointer()])
    {
      if(is_function_output(v, function, ns, false))
        function_map[function].modified_objects.insert(v);
    }
  }
  else if(is_function_output(expr, function, ns, false))
    function_map[function].modified_objects.insert(expr);
}

void ssa_heap_analysist::initialize(const goto_functionst &goto_functions)
{
  static_analysis_baset::initialize(goto_functions);

  if(goto_functions.function_map.at("main").body_available())
  {
    locationt e=goto_functions.function_map.at(
      "main").body.instructions.begin();
    ssa_heap_domaint &entry=operator[](e);

    entry.function=e->function;

    forall_goto_functions(f_it, goto_functions)
    {
      if(f_it->second.body_available())
      {
        locationt f_e=f_it->second.body.instructions.begin();
        ssa_heap_domaint &f_entry=operator[](f_e);
        for(auto &param : f_it->second.type.parameters())
        {
          entry.function_map[f_it->first].params.push_back(
            param.get_identifier());
          const symbol_exprt param_expr(param.get_identifier(), param.type());
          init_ptr_param(param_expr, f_entry);
        }
      }
    }
  }
}

void ssa_heap_analysist::init_ptr_param(
  const exprt &expr,
  ssa_heap_domaint &f_entry)
{
  const typet &type=ns.follow(expr.type());
  if(type.id()==ID_pointer)
  {
    const dereference_exprt dereference(expr, type.subtype());
    f_entry.value_map[expr].insert(dereference);
    init_ptr_param(dereference, f_entry);
  }
  else if(type.id()==ID_struct)
  {
    assert(expr.id()==ID_dereference);
    for(auto &component : to_struct_type(type).components())
    {
      if(component.type().id()==ID_pointer &&
         ns.follow(component.type().subtype())==type)
      {
        const member_exprt member(expr, component.get_name(), component.type());
        f_entry.value_map[member].insert(expr);
      }
    }
  }
}

const exprt ssa_heap_domaint::function_infot::corresponding_expr(
  const exprt &expr,
  const code_function_callt::argumentst &arguments,
  unsigned deref_level) const
{
  if(expr.id()==ID_symbol)
  {
    const irep_idt expr_id=to_symbol_expr(expr).get_identifier();
    exprt result=expr;
    for(std::size_t i=0; i<params.size(); ++i)
    {
      if(expr_id==params.at(i))
      {
        result=apply_deref(arguments.at(i), deref_level);
        break;
      }
    }
    return result;
  }
  else if(expr.id()==ID_dereference)
  {
    return corresponding_expr(
      to_dereference_expr(expr).pointer(),
      arguments,
      deref_level+1);
  }
  else if(expr.id()==ID_member)
  {
    return corresponding_expr(
      to_member_expr(expr).compound(),
      arguments,
      deref_level);
  }

  assert(false);
  return nil_exprt();
}

const exprt ssa_heap_domaint::function_infot::apply_deref(
  const exprt &expr,
  unsigned level) const
{
  if(level==0)
    return expr;

  exprt deref;
  if(expr.id()==ID_address_of)
  {
    deref=to_address_of_expr(expr).object();
  }
  else if(expr.id()==ID_symbol || expr.id()==ID_dereference)
  {
    deref=dereference_exprt(expr, expr.type().subtype());
  }
  else if(expr.id()==ID_member &&
          to_member_expr(expr).compound().id()==ID_dereference)
  {
    deref=to_member_expr(expr).compound();
  }
  else
    assert(false);

  return apply_deref(deref, level-1);
}
