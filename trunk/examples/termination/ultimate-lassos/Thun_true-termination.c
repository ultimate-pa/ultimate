/*
 * Date: 2012-03-05
 * Author: leike@informatik.uni-freiburg.de, heizmann@informatik.uni-freiburg.de
 *
 * Does not have a linear ranking function, but two succesive loop iterations
 * have a linear ranking function.
 * 
 * Some possible sequence of states
 * x  100 100  99 100  97 102  91 112  69  154 -17
 * y    0  -1   1  -3   5 -11  21 -43  85 -171 341
 * 
 * Some possible sequence of states in a version where we replace x:=x+y by x:=x-y.
 * x  100 100 101 100 103  98 109  88 131   44 215
 * y    0  -1   1  -3   5 -11  21 -43  85 -171 341
 * 
 */

extern int __VERIFIER_nondet_int();

int main()
{
	int x = __VERIFIER_nondet_int();
	int y = __VERIFIER_nondet_int();
	while (x >= 0) {
		x = x + y;
		y = (-2)*y - 1;
	}
	return 0;
}
