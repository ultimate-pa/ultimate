//#Safe
// Author: heizmann@informatik.uni-freiburg.de
// Date: 2022-11-15

extern unsigned long __VERIFIER_nondet_ulong();

int main() {
	// largest possible value
	unsigned __int128 largestUint128  = -1;
	// get some long
	unsigned long someULong = __VERIFIER_nondet_ulong();
	//@ assert largestUint128 > someULong;
	return 0;
}
