#include <assert.h>

extern int __VERIFIER_nondet_int();

int ssl3_connect(void) 
{
  int s__state ;
  int blastFlag ;

  s__state = 12292;
  blastFlag = 0;

  while (1) {
    if (s__state == 12292) {
      goto switch_1_12292;
    } else {
      if (s__state == 4368) {
	goto switch_1_4368;
      } else {
	if (s__state == 4384) {
	  goto switch_1_4384;
	} else {
	  if (s__state == 4400) {
	    goto switch_1_4400;
	  } else {
	    return 0;
	    if (0) {
	    switch_1_12292: /* CIL Label */ 
	      s__state = 4368;
	      continue;
	    switch_1_4368: /* CIL Label */ ;
	      blastFlag++;
	      s__state = 4384;
	      continue;
	    switch_1_4384: /* CIL Label */ ;
	      blastFlag++;
	      s__state = 4400;
	      continue;
	    switch_1_4400: /* CIL Label */ ;
	      if (blastFlag == 2) {
		break;
	      }
	      continue;
	    } 
	  }
	}
      }
    }
  }
  assert(0);
  return -1;
}
int main(void) 
{
  ssl3_connect();
  return 0;
}

/*
We get hoisted assertion:
(C) $guard#ls50%2 && ($cond#22%2 || $cond#36%2 || $cond#49%2) ==> ($guard#51 ==> FALSE)

But $cond#36%2 is a return and no break condition!
*/
