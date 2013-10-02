//#iSafe
/*
 * Date: September 2013
 * Author: heizmann@informtik.uni-freiburg.de
 * 
 */

int nonMain(int *p, int *q, int *r) {
	*p = 23;
	*q = 42;
	*r = 101;
	if (*p == 42) {
		//@ assert p == q;
	} else {
		if (*p == 101) {
			//@ assert r == p;
		} else {
			//@ assert r != p && p != q;
		}
	}
}
