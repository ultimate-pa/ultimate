/*
 * Date: 2012-02-18
 * Author: heizmann@informatik.uni-freiburg.de
 *
 */

extern int __VERIFIER_nondet_int(void);

int main()
{
	int x = __VERIFIER_nondet_int();
	int y = __VERIFIER_nondet_int();
	while (x >= 0 && y >= 0) {
		int old_x = x;
		x = y - 1;
		y = old_x - 1;
	}
	return 0;
}

