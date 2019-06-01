#include <assert.h>

void copy_authority(
  char *uri,
  int uri_length,
  int authority_start,
  char *authority)
{
  __CPROVER_assume(0 < uri_length);
  __CPROVER_assume(0 < authority_start && authority_start < uri_length);
  int cp = authority_start;
  while (cp != uri_length - 1)
  {
    if (uri[cp] == '/')
      break;
    assert(cp < uri_length);
    authority[cp - authority_start] = uri[cp];
    ++cp;
  }
}
