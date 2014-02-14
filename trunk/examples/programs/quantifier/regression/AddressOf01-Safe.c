//#Safe
/*
 * Date: September 2013
 * Author: heizmann@informtik.uni-freiburg.de
 * 
 */

int nonMain() {
	int x;
        int *p = &x;
	//@ assert 3 == 3;
}
