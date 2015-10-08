/*******************************************************************\

Module: Command Line Interface

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_DELTACHECK_CALL_GRAPH_H
#define CPROVER_DELTACHECK_CALL_GRAPH_H

#include <util/xml.h>
#include <analyses/call_graph.h>

void summary_to_call_graph(const xmlt &xml, call_grapht &dest);

#endif
