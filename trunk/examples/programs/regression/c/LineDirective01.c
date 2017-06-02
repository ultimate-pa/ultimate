//#Safe
/* 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2017-05-09
 * 
 */

extern void __VERIFIER_error() __attribute__ ((__noreturn__));
extern int __VERIFIER_nondet_int();

int main() {
    int x = 0;
	if (__VERIFIER_nondet_int()) {
		#line 999899799
		__VERIFIER_error();
	} else {
		#line 7 "IBims1NicesAnderesFile.c"
		__VERIFIER_error();
	}
	return 0;
}
