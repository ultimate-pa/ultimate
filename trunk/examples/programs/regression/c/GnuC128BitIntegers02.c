//#Unsafe
// Author: heizmann@informatik.uni-freiburg.de
// Date: 2022-11-15

extern unsigned long long __VERIFIER_nondet_ulonglong();
extern unsigned __int128 __VERIFIER_nondet_uint128();

int main() {
	// largest possible usigned long long
	unsigned long long largestUlonglong = 18446744073709551615ULL;
	unsigned __int128 someUint128  = __VERIFIER_nondet_uint128();
	//@ assert someUint128 <= largestUlonglong;
	return 0;
}
