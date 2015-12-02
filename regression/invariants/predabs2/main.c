#include "../cprover_templates.h"

void main()
{
  int a = 0;
  int b = 0;
  int x = 0;
  int y = 0;
  while(x<10)
  {
    __CPROVER_template(a == x);
    __CPROVER_template(x == y);
    __CPROVER_template(b == y);
    __CPROVER_template(b == a);
    x++;
    y++;
    if(x==y) a = x;
    if(x==a) b = a; //here transitivity of equalities is needed
  }
  assert(x==b);
}
