//#termcomp16-someonesaidyes
/*
 * Date: 06/07/2015
 * Created by: Ton Chanh Le (chanhle@comp.nus.edu.sg)
 * Adapted from Benghazi_true-termination.c
 */

typedef enum {false, true} bool;

extern int __VERIFIER_nondet_int(void);

int main()
{
    int x, d1, d2, d1old;
    x = __VERIFIER_nondet_int();
    d1 = __VERIFIER_nondet_int();
    d2 = __VERIFIER_nondet_int();
	while (x >= 0) {
		x = x - d1;
		d1old = d1;
		d1 = d2 + 1;
		d2 = d1old + 1;
	}
	return 0;
}
