#include "../cprover_templates.h"

void main()
{
  int x = 0;  

  while(x<10)
  {
    __CPROVER_template(x<=10);
    __CPROVER_template(x>0);
    x++;
    assert(x<=10);
  }

  assert(x==10);
}

