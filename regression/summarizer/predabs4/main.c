#include "../cprover_templates.h"

void main()
{
  int x = 0;  

  while(x<10)
  {
    __CPROVER_template(x<=10);
    __CPROVER_templat(x>0);
    __CPROVER_template(x < __CPROVER_template_newvar(x));
    __CPROVER_template(x >__CPROVER_template_newvar(x));
    x++;
    assert(x<=10);
  }

  assert(x==10);
}

