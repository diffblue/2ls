#include <assert.h>
#include <string.h>

struct str
{
  int x;
  int y;
  int z;
};

struct str pass_through_struct (int q)
{
  struct str s;
  memset(&s,0,sizeof(struct str));

  s.x += q;
  s.y += s.x;
  s.z += s.y;

  return s;
}

int main (void)
{
  int q;

  struct str s;

  s = pass_through_struct(q);

  assert(q == s.z);

  return 1;
}


