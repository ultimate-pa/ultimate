//#iSafe
/*
 * Date: September 2013
 * Author: heizmann@informtik.uni-freiburg.de
 * 
 */

int nonMain(int *p, int *q) {
	*p = 23;
	*q = 42;
	if (*p == 42) {
		//@ assert p == q;
	} else {
		//@ assert p != q;
	}
}
