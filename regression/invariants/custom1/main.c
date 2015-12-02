#include "../cprover_templates.h"

void main()
{
  int x = 0;  

  while(x<10)
  {
    __CPROVER_template(x<=__CPROVER_template_param_int());
    __CPROVER_template(-x<=__CPROVER_template_param_int());
    x++;
    assert(x<=10);
  }

  assert(x==10);
}

