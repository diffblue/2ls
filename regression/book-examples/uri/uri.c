#include <assert.h>

void extract_domain(char *uri, int uri_length, int uri_start, char *domain) {
  __CPROVER_assume(0 < uri_length);
  __CPROVER_assume(0 < uri_start && uri_start < uri_length);
  int cp = uri_start;
  while (cp != uri_length - 1) {
    if (uri[cp] == '/')
      break;
    assert(cp < uri_length);
    domain[cp] = uri[cp];
    ++cp;
  }
}
