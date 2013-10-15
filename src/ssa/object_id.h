/*******************************************************************\

Module: Strings from Objects

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_OBJECT_ID_H
#define CPROVER_OBJECT_ID_H

#include <util/expr.h>

// Returns unique string for object 'src',
// or empty string if 'src' is not an object.
irep_idt object_id(const exprt &src);

#endif
