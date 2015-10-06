/*
 * Date: 18.11.2012
 * Author: heizmann@informatik.uni-freiburg.de
 * 
 * Has ranking function f(x,d1,d2)=x for the invariant
 * d1 >=1 /\ d2>=1.
 * 
 * This lasso program has a 2-phase ranking function.
 *
 */

extern int __VERIFIER_nondet_int();

int main()
{
	int d1 = 73;
	int d2 = 74;
	int x = __VERIFIER_nondet_int();
	while (x >= 0) {
		x = x - d1;
		int d1_old = d1;
		d1 = d2 + 1;
		d2 = d1_old + 1;
	}
	return 0;
}
