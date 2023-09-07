//#Safe
// Author: heizmann@informatik.uni-freiburg.de
// Date: 2023-08-30

extern int __VERIFIER_nondet_int(void);
extern short __VERIFIER_nondet_short(void);

int main() {
	int x = __VERIFIER_nondet_short();
	int y = ({int a = x; a;});
	while (__VERIFIER_nondet_int()) {
	}
	//@ assert x == y;
	return 0;
}
