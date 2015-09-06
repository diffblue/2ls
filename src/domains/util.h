#ifndef CPROVER_DOMAIN_UTIL_H
#define CPROVER_DOMAIN_UTIL_H

#include <util/std_expr.h>
#include <util/namespace.h>
#include <util/arith_tools.h>
#include <util/ieee_float.h>
#include <langapi/language_util.h>
#include <iostream>

void extend_expr_types(exprt &expr);
constant_exprt simplify_const(const exprt &expr);
ieee_floatt simplify_const_float(const exprt &expr);
mp_integer simplify_const_int(const exprt &expr);
void merge_and(exprt & result, const exprt &expr1, const exprt &expr2, 
	       const namespacet &ns);


#endif
