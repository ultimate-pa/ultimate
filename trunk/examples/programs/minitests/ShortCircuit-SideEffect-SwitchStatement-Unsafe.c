//#Unsafe
// Author: heizmann@informatik.uni-freiburg.de
// Date: 4.2.2013
// apparently useless while loop is used to check that no auxilliary temporary
// variable occurs in a derived loop invariant

int main() {
    int x = 1;
    int y = 1;
    _Bool z;
    int a;
    switch( (x++ != 0) || (y++ == 0) ) {
        case (1 == 0):  
            z = 0;
	    while (a) { int b; a = b; }
	    break;
        case (0 == 0):    
            z = 1;
	    while (a) { int b; a = b; }
	    break;
	default:
	    z = 3;
	    while (a) { int b; a = b; }
    }
    //@ assert y == 2;
}
