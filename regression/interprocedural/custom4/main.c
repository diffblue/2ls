#include <assert.h>
#include <stdint.h>
#include "../cprover_templates.h"

int f00 (unsigned int n, int data[]) {
  __CPROVER_assume(n > 0);
  __CPROVER_assume(n < 255);

  int total = 0;
  unsigned int i = 0;
  uint64_t cost = 0;

  uint64_t costl1 = 0;
  for (i = 0; i < n; ++i, ++costl1) {
    __CPROVER_template(i <= __CPROVER_template_param_int());
    __CPROVER_template(-i <= __CPROVER_template_param_int());
    /*    __CPROVER_template(costl1 / n <= __CPROVER_template_param_int());
    __CPROVER_template(costl1 - i <= __CPROVER_template_param_int());
    __CPROVER_template(i - costl1 <= __CPROVER_template_param_int()); */
    __CPROVER_template(i - __CPROVER_template_newvar(i) <= __CPROVER_template_param_int());
    __CPROVER_template(__CPROVER_template_newvar(i) - i <= __CPROVER_template_param_int());
    total += data[i];
  }

  cost += costl1;

  assert(cost < 18446744073709551615ull);
  assert(cost / n <= 8);

  return total;
}

int main (void) {
  unsigned int n;
  int data[255];

  f00(n, data);

  return 0;
}
