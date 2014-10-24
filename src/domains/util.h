#ifndef CPROVER_DOMAIN_UTIL_H
#define CPROVER_DOMAIN_UTIL_H

#include <util/std_expr.h>
#include <util/arith_tools.h>
#include <util/ieee_float.h>
#include <langapi/language_util.h>
#include <iostream>

void extend_expr_types(exprt &expr);
constant_exprt simplify_const(const exprt &expr);
ieee_floatt simplify_const_float(const exprt &expr);
mp_integer simplify_const_int(const exprt &expr);
void pretty_print_termination_argument(std::ostream &out, 
				       const namespacet &ns, const exprt &expr);


#endif
