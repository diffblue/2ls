/*******************************************************************\

Module: Property Management

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "../html/html_escape.h"
#include "properties.h"

/*******************************************************************\

Function: report_properties

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void report_properties(
  const propertiest &properties,
  std::ostream &out)
{
  // produce clickable table of properties
  
  out << "<table class=\"properties\">\n";

  out << "<tr>"
      << "<th>Status</th>\n"
      << "<th colspan=2>Location</th>\n"
      << "<th colspan=2>Property</th>\n"
      << "</tr>\n\n";

  unsigned count;

  count=0;

  for(propertiest::const_iterator
      p_it=properties.begin();
      p_it!=properties.end();
      p_it++, count++)
  {
    const locationt &location=p_it->loc->location;
  
    out << "<tr class=\"property\""
           " onMouseOver=\"property_event(this,'over',null);\""
           " onMouseOut=\"property_event(this,'out',null);\""
           " onClick=\"property_event(this,'click',ce" << count << ");\""
           ">\n";
    
    out << "  <td align=\"center\">";
    
    if(p_it->status.is_false())
      out << "<font size=\"+1\" color=\"#CC0000\">&#x2717;</font>"
             "</td> <!-- fail -->\n"; // ✗
    else if(p_it->status.is_true())
      out << "<font size=\"+1\" color=\"#009933\">&#x2713;</font>"
             "</td> <!-- pass -->\n"; // ✓
    else
      out << "<font size=\"+1\" color=\"#FFCC00\">?</font>"
             "</td> <!-- unknown -->\n";
    
    out << "  <td>";
    out << html_escape(location.get_file());
    out << "</td>\n";

    out << "  <td>";
    out << html_escape(location.get_line());
    out << "</td>\n";
    
    out << "  <td>";
    out << html_escape(location.get_property());
    out << "</td>\n";
    
    out << "  <td>";
    out << html_escape(location.get_comment());
    out << "</td>\n";
    
    out << "</tr>\n\n";
  }
  
  out << "</table>\n\n";
}

/*******************************************************************\

Function: get_tracked_expr

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void get_tracked_expr(
  const exprt &src,
  std::list<exprt> &dest)
{
  forall_operands(it, src)
    get_tracked_expr(*it, dest);
    
  if(src.id()==ID_symbol)
    dest.push_back(src);
}

/*******************************************************************\

Function: get_tracked_expr_lhs

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void get_tracked_expr_lhs(
  const exprt &src,
  std::list<exprt> &dest_lhs,
  std::list<exprt> &dest_rhs)
{
  if(src.id()==ID_symbol)
    dest_lhs.push_back(src);
  else if(src.id()==ID_member)
  {
    get_tracked_expr_lhs(to_member_expr(src).struct_op(), dest_lhs, dest_rhs);
  }
  else if(src.id()==ID_index)
  {
    get_tracked_expr_lhs(to_index_expr(src).array(), dest_lhs, dest_rhs);
    get_tracked_expr(to_index_expr(src).index(), dest_rhs);
  }
  else
    get_tracked_expr(src, dest_rhs);
}

/*******************************************************************\

Function: report_countermodel

  Inputs:

 Outputs:

 Purpose: this produces counterexample values as JavaScript

\*******************************************************************/

void report_countermodel(
  const propertyt &property,
  const function_SSAt &function_SSA,
  unsigned count,
  std::ostream &out)
{
  for(propertyt::value_mapt::const_iterator
      v_it=property.value_map.begin();
      v_it!=property.value_map.end();
      v_it++)
  {
    out << "// " << from_expr(function_SSA.ns, "", v_it->first)
                 << " -> "
                 << from_expr(function_SSA.ns, "", v_it->second)
                 << "\n";
  }
  
  std::map<std::string, unsigned> var_count;

  forall_goto_program_instructions(i_it, function_SSA.goto_function.body)
  {
    std::list<exprt> tracked_expr_rhs, tracked_expr_lhs;
    
    if(i_it->is_assert() || i_it->is_assume() || i_it->is_goto())
    {
      get_tracked_expr(i_it->guard, tracked_expr_rhs);
    }
    else if(i_it->is_assign())
    {
      const code_assignt &code_assign=to_code_assign(i_it->code);
      get_tracked_expr_lhs(code_assign.lhs(), tracked_expr_lhs, tracked_expr_rhs);
      get_tracked_expr(code_assign.rhs(), tracked_expr_rhs);
    }
    
    // lhs
    for(std::list<exprt>::const_iterator
        e_it=tracked_expr_lhs.begin();
        e_it!=tracked_expr_lhs.end();
        e_it++)
    {
      exprt input_name=function_SSA.name_input(to_symbol_expr(*e_it));
      exprt renamed_lhs=function_SSA.read_lhs(*e_it, i_it);

      const propertyt::value_mapt::const_iterator v_it_lhs=
        property.value_map.find(renamed_lhs);

      if(v_it_lhs!=property.value_map.end())
      {
        std::string var=from_expr(function_SSA.ns, "", input_name);
        std::string var_loc=var+"@"+id2string(i_it->location.get_line());
        out << "ce" << count << "['" << var_loc
            << "." << ++var_count[var_loc]
            << "']='"
            << from_expr(function_SSA.ns, "", v_it_lhs->second)
            << "';\n";
      }
    }

    // rhs
    for(std::list<exprt>::const_iterator
        e_it=tracked_expr_rhs.begin();
        e_it!=tracked_expr_rhs.end();
        e_it++)
    {
      exprt input_name=function_SSA.name_input(to_symbol_expr(*e_it));
      exprt renamed_rhs=function_SSA.read_rhs(*e_it, i_it);

      const propertyt::value_mapt::const_iterator v_it_rhs=
        property.value_map.find(renamed_rhs);
        
      if(v_it_rhs!=property.value_map.end())
      {
        std::string var=from_expr(function_SSA.ns, "", input_name);
        std::string var_loc=var+"@"+id2string(i_it->location.get_line());
        out << "ce" << count << "['" << var_loc
            << "." << ++var_count[var_loc]
            << "']='"
            << from_expr(function_SSA.ns, "", v_it_rhs->second)
            << "';\n";
      }

    }
  }
}

/*******************************************************************\

Function: report_countermodels

  Inputs:

 Outputs:

 Purpose: this produces counterexample values as JavaScript

\*******************************************************************/

void report_countermodels(
  const function_SSAt &function_SSA_old,
  const function_SSAt &function_SSA_new,
  const propertiest &properties,
  std::ostream &out)
{
  out << "<script type=\"text/javascript\">\n";
  out << "// differential countermodels\n";
  
  unsigned count=0;
  
  for(propertiest::const_iterator
      p_it=properties.begin();
      p_it!=properties.end();
      p_it++, count++)
  {
    out << "var ce" << count << " = { };\n";

    const propertyt &property=*p_it;
    
    if(property.status==tvt(false))
    {
      report_countermodel(*p_it, function_SSA_old, count, out);
      report_countermodel(*p_it, function_SSA_new, count, out);
    }
    
    out << "\n";
  }

  out << "</script>\n\n";
}

/*******************************************************************\

Function: report_countermodels

  Inputs:

 Outputs:

 Purpose: this produces counterexample values as JavaScript

\*******************************************************************/

void report_countermodels(
  const function_SSAt &function_SSA,
  const propertiest &properties,
  std::ostream &out)
{
  out << "<script type=\"text/javascript\">\n";
  out << "// single-version countermodels\n";
  
  unsigned count=0;
  
  for(propertiest::const_iterator
      p_it=properties.begin();
      p_it!=properties.end();
      p_it++, count++)
  {
    out << "var ce" << count << " = { };\n";

    const propertyt &property=*p_it;
    
    if(property.status==tvt(false))
    {
      report_countermodel(*p_it, function_SSA, count, out);
    }
    
    out << "\n";
  }

  out << "</script>\n\n";
}

