/*
 * Date: 2012-12-14
 * Author: Jan Leike and heizmann@informatik.uni-freiburg.de
 *
 * Has linear ranking function f(x)=x with supporting invariant
 * (y>=100 /\ z=1) \/ (y>=99 /\ z=1).
 * However, there is no linear supporting invariant for this ranking function.
 * 
 * Has a three phase ranking function.
 */

extern int __VERIFIER_nondet_int(void);

int main()
{
	int x = __VERIFIER_nondet_int();
	int y = 100;
	int z = 1;
	while (x >= 0) {
		x = x - y;
		y = y - z;
		z = -z;
	}
	return 0;
}
