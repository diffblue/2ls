#include "../cprover_templates.h"

void main()
{
  int a = 0;
  int b = 0;
  int x = 0;
  int y = 0;
  while(x<3 && y<3)
  {
    __CPROVER_template(x == y);
    __CPROVER_template(y <= 3);
    x++;
    y++;
  }

  assert(x * y <= 10);
}
