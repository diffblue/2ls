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
    const optionst &_options,
    std::ostream &_out):
    goto_functions(_goto_model.goto_functions),
    symbol_table(_goto_model.symbol_table),
    ns(_goto_model.symbol_table),
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
  const optionst &options;
  std::ostream &out;

  smt2_convt smt2_conv;

  void translate(const goto_functionst::function_mapt::const_iterator);
};

void horn_encodingt::operator()()
{
  forall_goto_functions(f_it, goto_functions)
    translate(f_it);
}

void horn_encodingt::translate(
  const goto_functionst::function_mapt::const_iterator f_it)
{
  if(f_it->second.body.empty())
    return;

  out << "\n"
         ";\n"
         "; Function " << f_it->first << "\n"
         ";\n";

  // compute SSA
  local_SSAt local_SSA(f_it->second, symbol_table, options, "");

  const goto_programt &body=f_it->second.body;

  // first generate the predicates for all locations
  for(goto_programt::instructionst::const_iterator
      loc=body.instructions.begin();
      loc!=body.instructions.end();
      loc++)
  {
    out << "(declare-fun h-" << f_it->first << "-"
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
    out << "  (=> (h-" << f_it->first << '-'
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
        out << "(h-" << f_it->first << '-'
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

        out << "(h-" << f_it->first << '-'
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
  const optionst &options,
  std::ostream &out)
{
  horn_encodingt(goto_model, options, out)();
}
