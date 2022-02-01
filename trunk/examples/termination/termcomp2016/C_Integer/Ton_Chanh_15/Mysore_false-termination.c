//#termcomp16-someonesaidno
/*
 * Date: 06/07/2015
 * Created by: Ton Chanh Le (chanhle@comp.nus.edu.sg)
 * Adapted from Mysore_true-termination.c
 */

typedef enum {false, true} bool;

extern int __VERIFIER_nondet_int(void);

int main()
{
	int x;
	int c;
    x = __VERIFIER_nondet_int();
    c = __VERIFIER_nondet_int();
	if (c < 0) {
    	while (x + c >= 0) {
	    	x = x - c;
		    c = c - 1;
	    }
	}
	return 0;
}
