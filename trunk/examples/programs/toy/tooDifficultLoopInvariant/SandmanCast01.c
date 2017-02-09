//#Safe
/*
 * Date: 2017-02-07
 * Author: heizmann@informatik.uni-freiburg.de
 *
 *
 *
 */

extern int __VERIFIER_nondet_int(void);

int main() {
	int i = __VERIFIER_nondet_int();
	signed char c = i;
	unsigned int j = __VERIFIER_nondet_uint();
	unsigned long x = 128 + c;
	unsigned long y = 128 + j;
	if (c < 0) {
		//@ assert x != y;
	}
	return 0;
}
