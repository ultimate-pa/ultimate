/*
 * Program from the example depicted in the introduction of
 * 2014TACAS - Chen,Cook,Fuhs,Nimkar,O’Hearn - Proving Nontermination via Safety
 *
 * Date: 2014-06-28
 * Author: Matthias Heizmann
 *
 */

extern int __VERIFIER_nondet_int(void);

int main() {
	int k = __VERIFIER_nondet_int();
	int i = __VERIFIER_nondet_int();
	if (k >= 0) {
		// skip
	} else {
		i = -1;
	}
	while (i >= 0) {
		i = __VERIFIER_nondet_int();
	}
	i = 2;
	return 0;
}