/* #Unsafe
 * 
 * Variables initialized with __VERIFIER_nondet_int which returns 
 * nondeterministically some value.
 * We may not assume that we obtain that the same value for a in each 
 * iteration.
 * 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 12.10.2013
 * 
 */

extern void __VERIFIER_error() __attribute__ ((__noreturn__));
extern int __VERIFIER_nondet_int();

int main() {
	int x = 0;
	int i = 0;
	while (i<2) {
		int a = __VERIFIER_nondet_int();;
		if (i == 0) {
			x = a;
		} else {
			//@ assert x == a;
		}
		i++;
	}
}
