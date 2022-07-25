/*******************************************************************\

Module: Horn-clause Encoding

Author: Daniel Kroening

\*******************************************************************/

/// \file
/// Horn-clause Encoding

#include <ostream>

#include <solvers/smt2/smt2_conv.h>

#include <ssa/local_ssa.h>

#include "horn_encoding.h"

class horn_encodingt
{
public:
  horn_encodingt(
    const goto_modelt &_goto_model,
    dynamic_objectst &_dynamic_objects,
    const optionst &_options,
    std::ostream &_out):
    goto_functions(_goto_model.goto_functions),
    symbol_table(_goto_model.symbol_table),
    ns(_goto_model.symbol_table),
    dynamic_objects(_dynamic_objects),
    options(_options),
    out(_out),
    smt2_conv(ns, "", "Horn-clause encoding", "", smt2_convt::solvert::Z3, _out)
  {
  }

  void operator()();

protected:
  const goto_functionst &goto_functions;
  const symbol_tablet &symbol_table;
  const namespacet ns;
  dynamic_objectst &dynamic_objects;
  const optionst &options;
  std::ostream &out;

  smt2_convt smt2_conv;

  void translate(const irep_idt &function_id, const goto_functiont &function);
};

void horn_encodingt::operator()()
{
  for(const auto &f_it : goto_functions.function_map)
    translate(f_it.first, f_it.second);
}

void horn_encodingt::translate(
  const irep_idt &function_id,
  const goto_functiont &function)
{
  if(function.body.empty())
    return;

  out << "\n"
         ";\n"
         "; Function " << function_id << "\n"
         ";\n";

  // compute SSA
  local_SSAt local_SSA(
    function_id,
    function,
    symbol_table,
    dynamic_objects,
    options,
    "");

  const goto_programt &body=function.body;

  // first generate the predicates for all locations
  for(goto_programt::instructionst::const_iterator
      loc=body.instructions.begin();
      loc!=body.instructions.end();
      loc++)
  {
    out << "(declare-fun h-" << function_id << "-"
        << loc->location_number << " (";

    for(ssa_objectst::objectst::const_iterator
        o_it=local_SSA.ssa_objects.objects.begin();
        o_it!=local_SSA.ssa_objects.objects.end();
        o_it++)
    {
      if(o_it!=local_SSA.ssa_objects.objects.begin())
        out << ' ';
      out << '(';
      smt2_conv.convert_expr(o_it->symbol_expr());
      out << ' ';
      smt2_conv.convert_type(o_it->type());
      out << ')';
    }

    out << ") Bool)\n";
  }

  out << '\n';

  // now encode transitions
  for(goto_programt::instructionst::const_iterator
      loc=body.instructions.begin();
      loc!=body.instructions.end();
      loc++)
  {
#if 0
    const local_SSAt::nodet &node=*local_SSA.find_node(loc);
#endif
    out << "; PC " << loc->location_number
        << " " << loc->source_location << '\n';

    out << "(assert (forall (";

    for(ssa_objectst::objectst::const_iterator
        o_it=local_SSA.ssa_objects.objects.begin();
        o_it!=local_SSA.ssa_objects.objects.end();
        o_it++)
    {
      if(o_it!=local_SSA.ssa_objects.objects.begin())
        out << ' ';
      out << '(';
      smt2_conv.convert_expr(o_it->symbol_expr());
      out << ' ';
      smt2_conv.convert_type(o_it->type());
      out << ')';
    }

    out << ")\n";
    out << "  (=> (h-" << function_id << '-'
        << loc->location_number;

    for(ssa_objectst::objectst::const_iterator
        o_it=local_SSA.ssa_objects.objects.begin();
        o_it!=local_SSA.ssa_objects.objects.end();
        o_it++)
    {
      out << ' ';
      smt2_conv.convert_expr(o_it->symbol_expr());
    }

    out << ")\n      ";

    if(loc->is_goto())
    {
      if(loc->guard.is_true())
      {
        out << "(h-" << function_id << '-'
            << loc->get_target()->location_number;

        for(ssa_objectst::objectst::const_iterator
            o_it=local_SSA.ssa_objects.objects.begin();
            o_it!=local_SSA.ssa_objects.objects.end();
            o_it++)
        {
          out << ' ';
          smt2_conv.convert_expr(o_it->symbol_expr());
        }

        out << ')';
      }

      if(!loc->guard.is_true())
      {
        goto_programt::instructionst::const_iterator next=loc;
        next++;

        out << "(h-" << function_id << '-'
            << loc->get_target()->location_number;

        for(ssa_objectst::objectst::const_iterator
            o_it=local_SSA.ssa_objects.objects.begin();
            o_it!=local_SSA.ssa_objects.objects.end();
            o_it++)
        {
          out << ' ';
          smt2_conv.convert_expr(o_it->symbol_expr());
        }

        out << ')';
      }
    }
    else if(loc->is_function_call())
    {
    }
    else
    {
      #if 0
      for(local_SSAt::nodet::constraintst::const_iterator
          it=node.constraints.begin();
          it!=node.constraints.end();
          it++)
      {
        smt2_conv.set_to(*it, true);
      }
      #endif

      #if 0
      for(local_SSAt::nodet::equalitiest::const_iterator
          it=node.equalities.begin();
          it!=node.equalities.end();
          it++)
      {
        smt2_conv.set_to(*it, true);
      }
      #endif
    }

    out << ")))"; // =>, forall, assert

    out << '\n';
  }
}

void horn_encoding(
  const goto_modelt &goto_model,
  dynamic_objectst &dynamic_objects,
  const optionst &options,
  std::ostream &out)
{
  horn_encodingt(goto_model, dynamic_objects, options, out)();
}
