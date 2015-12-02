#include "../cprover_templates.h"

void main()
{
  int x = 0, y = 0;  

  while(x<10)
  {
    __CPROVER_template(x<=__CPROVER_template_param_int());
    __CPROVER_template(-x<=__CPROVER_template_param_int());
    __CPROVER_template(y<=__CPROVER_template_param_int());
    __CPROVER_template(-y<=__CPROVER_template_param_int());
    __CPROVER_template(2*x-y<=__CPROVER_template_param_int());
    __CPROVER_template(-(2*x-y)<=__CPROVER_template_param_int());
    x++;
    y+=2;
  }

  assert(x==10);
  assert(y==20);
}

