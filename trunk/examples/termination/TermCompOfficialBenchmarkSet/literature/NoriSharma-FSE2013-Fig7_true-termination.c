/*
 * Program from Fig.7 of
 * 2013FSE - Nori,Sharma - Termination Proofs from Tests
 *
 * Date: 18.12.2013
 * Author: heizmann@informatik.uni-freiburg.de
 *
 */

extern int __VERIFIER_nondet_int(void);

int main() {
	int i = __VERIFIER_nondet_int();
	int j = __VERIFIER_nondet_int();
	int M = __VERIFIER_nondet_int();
	int N = __VERIFIER_nondet_int();
	int a, b, c;
    a = i;
    b = j;
    c = 0;
    while (i<M || j<N) {
    	i = i + 1;
    	j = j + 1;
    	c = c + 1;
    }
}
