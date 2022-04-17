extern int __VERIFIER_nondet_int();
/*
 * Simpler regression reproducer inspired by nondet_free_kind
 */
#include <stdlib.h>

typedef struct node {
  struct node* next;
  struct node* prev;
} *DLL;

void myexit(int s) {
 _EXIT: goto _EXIT;
}

DLL dll_circular_create(int len) {
  DLL last = (DLL) malloc(sizeof(struct node));
  if(NULL == last) {
    myexit(1);
  }
  last->next = last;
  last->prev = last;
  DLL head = last;
  while(len > 1) {
    DLL new_head = (DLL) malloc(sizeof(struct node));
    if(NULL == new_head) {
      myexit(1);
    }
    new_head->next = head;
    head->prev = new_head;
    head = new_head;
    len--;
  }
  last->next = head;
  head->prev = last;
  return head;
}

void _destroy(DLL head) {
  free(head);
}

int main() {
  const int len = 2;
  DLL head = dll_circular_create(len);
  /* next function call causes memory leak */
  _destroy(head);
  head = NULL;
  return 0;
}
