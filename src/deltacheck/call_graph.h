/*******************************************************************\

Module: Command Line Interface

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_DELTACHECK_CALL_GRAPH_H
#define CPROVER_DELTACHECK_CALL_GRAPH_H

#include <iostream>
#include <map>

#include <util/irep.h>
#include <util/xml.h>

class call_grapht:std::multimap<irep_idt, irep_idt>
{
public:
  void add_summary(const xmlt &xml);
  void output_dot(std::ostream &out) const;
};

#endif
