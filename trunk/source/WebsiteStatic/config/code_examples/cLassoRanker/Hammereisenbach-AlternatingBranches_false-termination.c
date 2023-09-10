//#rNonTermination
/* 
 * Nonterminating execution alternates between two branches.
 * Date: 2016-07-26
 * Author: heizmann@informatik.uni-freiburg.de
 */


extern int __VERIFIER_nondet_int(void);

int main()
{
	int x;
	x = __VERIFIER_nondet_int();
    while (1) {
		if (x % 2 == 0) {
			x = x - 1;
		} else {
			x = x - 1;
		}
    }
	return 0;
}
