/*
 * Program from Fig.1 of
 * 2012SAS - Chen,Flur,Mukhopadhyay - Termination Proofs for Linear Simple Loops
 *
 * Date: 2013-12-18
 * Author: heizmann@informatik.uni-freiburg.de
 *
 */

extern int __VERIFIER_nondet_int(void);

int main() {
	int x,y,z;
	x = __VERIFIER_nondet_int();
	y = __VERIFIER_nondet_int();
	z = __VERIFIER_nondet_int();
	while (x > 0) {
		x = x + y;
		y = z;
		z = -z -1;
	}
}
