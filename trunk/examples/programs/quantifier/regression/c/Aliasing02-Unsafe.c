//#Unsafe
/*
 * Date: September 2013
 * Author: heizmann@informatik.uni-freiburg.de
 * 
 */

int nonMain(int *p, int *q) {
	*p = 23;
	*q = 42;
	if (*p == 23) {
		//@ assert \false;
	}
}
