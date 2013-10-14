//#iSafe
/*
 * Date: October 2013
 * Author: heizmann@informtik.uni-freiburg.de
 * 
 */

int nonMain() {
    int* a; // some auxiliary statement to obtain memory model
    int b = *a; // some auxiliary statement to obtain memory model
	
    int *p = 0;
    int *q = 0;
    //@ assert p == q;
    return 0;
}
