//#termcomp16-someonesaidno
/*
 * Date: 06/07/2015
 * Created by: Ton Chanh Le (chanhle@comp.nus.edu.sg)
 * Adapted from Cairo_true-termination.c
 */

typedef enum {false, true} bool;

extern int __VERIFIER_nondet_int(void);

int main()
{
    int x;
    x = __VERIFIER_nondet_int();
	if (x > __VERIFIER_nondet_int()) {
    	while (x != 0) {
	    	x = x - 1;
    	}
	}
	return 0;
}
