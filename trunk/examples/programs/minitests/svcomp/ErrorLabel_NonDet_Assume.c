//#mUnsafe
// Author: lindenmm@informatik.uni-freiburg.de
// Date: 16.08.2012

int main();
int bar(int y);

int main() {
	int x;
	x = __VERIFIER_nondet_int();
	int y = __VERIFIER_nondet_short();
	LABEL: ERROR: x = bar(x);
	if (x < 1000) {
		goto ERROR;
		goto LABEL;
		//@assert x == 1;
	}

	HIER: {
		TEST:
		x++;
	}

	__VERIFIER_assume(x == 1000);
	//@assert x==999;
}

int bar(int y) {
	return ++y;
}
