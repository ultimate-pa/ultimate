/*
 * Slightly modified version of the Waldkirch example where we currently fail 
 * to prove termination because our synthesis of ranking functions does not 
 * yet compute the integral hull of the transition relation.
 * Date: 2017-03-11
 * Author: heizmann@informatik.uni-freiburg.de
 *
 */

extern unsigned int __VERIFIER_nondet_uint(void);

int main()
{
	unsigned int x = __VERIFIER_nondet_uint();
	while (x >= 1) {
		x = x - 1;
	}
	return 0;
}
