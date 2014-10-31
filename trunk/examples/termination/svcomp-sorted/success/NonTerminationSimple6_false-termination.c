/*
 * Date: 2014-06-26
 * Author: leike@informatik.uni-freiburg.de
 */

extern int __VERIFIER_nondet_int();

const int c = 5;

int main()
{
	int x = __VERIFIER_nondet_int();
	while (x >= 0) {
		x += c;
	}
	return 0;
}

