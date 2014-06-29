/*
 * Date: 2014-06-26
 * Author: leike@informatik.uni-freiburg.de
 */

extern int __VERIFIER_nondet_int();

int main()
{
	int x = __VERIFIER_nondet_int();
	int c = __VERIFIER_nondet_int();
	
	if (c != 0) {
		return 1;
	}
	while (x >= 0) {
		x += c;
	}
	return 0;
}

