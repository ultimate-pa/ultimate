//#termcomp16-someonesaidyes
/*
 * Program from Fig.7 of
 * 2013FSE - Nori,Sharma - Termination Proofs from Tests
 *
 * Date: 18.12.2013
 * Author: heizmann@informatik.uni-freiburg.de
 *
 */

typedef enum {false, true} bool;

extern int __VERIFIER_nondet_int(void);

int main() {
	int a, b, c, i, j, M, N;
	i = __VERIFIER_nondet_int();
	j = __VERIFIER_nondet_int();
	M = __VERIFIER_nondet_int();
	N = __VERIFIER_nondet_int();
    a = i;
    b = j;
    c = 0;
    while (i<M || j<N) {
    	i = i + 1;
    	j = j + 1;
    	c = c + 1;
    }
    return 0;
}
