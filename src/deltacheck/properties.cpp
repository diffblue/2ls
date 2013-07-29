/*******************************************************************\

Module: Property Management

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "properties.h"
#include "html_escape.h"

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
    for(function_SSAt::objectst::const_iterator
        o_it=function_SSA.objects.begin();
        o_it!=function_SSA.objects.end();
        o_it++)
    {
      exprt input_name=function_SSA.name_input(*o_it);
    
      // lhs
      exprt renamed_lhs=function_SSA.read_lhs(*o_it, i_it);

      const propertyt::value_mapt::const_iterator v_it_lhs=
        property.value_map.find(renamed_lhs);

      if(function_SSA.assigns(*o_it, i_it) &&
         v_it_lhs!=property.value_map.end())
      {
        std::string var=from_expr(function_SSA.ns, "", input_name);
        std::string var_loc=var+"@"+id2string(i_it->location.get_line());
        out << "ce" << count << "['" << var_loc
            << "." << ++var_count[var_loc]
            << "']='"
            << from_expr(function_SSA.ns, "", v_it_lhs->second)
            << "';\n";
      }

      // rhs

      exprt renamed_rhs=function_SSA.read_rhs(*o_it, i_it);

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
  
  unsigned count=0;
  
  for(propertiest::const_iterator
      p_it=properties.begin();
      p_it!=properties.end();
      p_it++, count=0)
  {
    const propertyt &property=*p_it;
    
    if(property.status!=tvt(false)) continue;

    out << "var ce" << count << " = { };\n";

    report_countermodel(*p_it, function_SSA_old, count, out);
    report_countermodel(*p_it, function_SSA_new, count, out);
    
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
  
  unsigned count=0;
  
  for(propertiest::const_iterator
      p_it=properties.begin();
      p_it!=properties.end();
      p_it++, count=0)
  {
    const propertyt &property=*p_it;
    
    if(property.status!=tvt(false)) continue;

    out << "var ce" << count << " = { };\n";

    report_countermodel(*p_it, function_SSA, count, out);
    
    out << "\n";
  }

  out << "</script>\n\n";
}

