/*
 * Date: 06/07/2015
 * Created by: Ton Chanh Le (chanhle@comp.nus.edu.sg)
 * Adapted from Cairo_true-termination.c
 */

typedef enum {false, true} bool;

extern int __VERIFIER_nondet_int(void);

int main()
{
    int x, y;
	if (x > 0) {
	    while ((x != 0) && (y % 2 == 0)) {
	    	x = x + 2;
	    	y=y+2;
    	}
	}
	return 0;
}
