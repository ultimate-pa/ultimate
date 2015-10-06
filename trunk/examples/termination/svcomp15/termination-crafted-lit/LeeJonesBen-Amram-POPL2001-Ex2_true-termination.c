/*
 * Program from Ex.2 of
 * 2001POPL - Lee,Jones,Ben-Amram - The size-change principle for program termination
 * where we abstracted lists by their size.
 *
 * Date: 12.12.2013
 * Author: heizmann@informatik.uni-freiburg.de
 *
 */

extern int __VERIFIER_nondet_int(void);

int f(int i, int x);

int g(int a, int b, int c);

int f(int i, int x) {
	if (i==0) {
		return x;
	} else {
		return g(i-1,x,i);
	}
}

int g(int a, int b, int c) {
	return f(a,b+c);
}

int main() {
	int i = __VERIFIER_nondet_int();
	int x = __VERIFIER_nondet_int();
	if ( i >= 0 && x >= 0) {
		f(i,x);
	}
	return 0;
}
