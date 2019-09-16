//#rNonTermination
/* 
 * Example created by Sebastian Ott while he was visiting Freiburg.
 * Date: 2016-07-26
 * Author: heizmann@informatik.uni-freiburg.de
 */


extern int __VERIFIER_nondet_int(void);

int main()
{
	int x;
	x = 5;
    while (x != 0) {
		if (x < 0) {
			x = x + 20;
		}
		x = x - 2;
    }
	return 0;
}
