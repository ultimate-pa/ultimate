//#iSafe
/*
 * Date: October 2013
 * Author: heizmann@informtik.uni-freiburg.de
 * 
 */

int nonMain() {
    int* a; // some auxiliary statement to obtain memory model
    int b = *a; // some auxiliary statement to obtain memory model
	
    // Case 1: assigned at declaration
    int *p = 0;
    
    // Case 2: assigned later
    int *q;
    q = 0;
    
    //@ assert p == q;

    return 0;
}
