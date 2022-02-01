//#Unsafe
/* 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2015-11-06
 * 
 * Sequence of conversions in which a vale is converted to the largest vale
 * of unsigned integer types.
 * Using the Nutz Transformation, we always use -1 as representative for the
 * value. This examples is used to check if we output reasonable values in
 * the failure path or in a witness.
 * Yet, this cannot be checked by our testframework and we have to inspect 
 * values manually.
 */

extern int __VERIFIER_nondet_int();

int main() {
	long long a = -1;
	while(__VERIFIER_nondet_int()) {
		// do nothing, break large block encoding
	}
	unsigned long long b = a;
	while(__VERIFIER_nondet_int()) {
		// do nothing, break large block encoding
	}
	unsigned long c = b;
	while(__VERIFIER_nondet_int()) {
		// do nothing, break large block encoding
	}
	unsigned int d = c;
	while(__VERIFIER_nondet_int()) {
		// do nothing, break large block encoding
	}
	unsigned short e = d;
	while(__VERIFIER_nondet_int()) {
		// do nothing, break large block encoding
	}
	unsigned char f = e;
	while(__VERIFIER_nondet_int()) {
		// do nothing, break large block encoding
	}
	_Bool g = f;
	if (g) {
		//@ assert \false;
	}
	return 0;
}