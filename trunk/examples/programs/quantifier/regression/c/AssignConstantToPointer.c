//#Safe
/*
 * Date: October 2013
 * Author: heizmann@informatik.uni-freiburg.de
 * 
 */

#include <stdlib.h>

typedef struct fraction {
	int num;
	int denom;
} *fractionPtr;


int main() {
    int* a = malloc(sizeof(int)); // some auxiliary statement to obtain memory model
    int b = *a; // some auxiliary statement to obtain memory model
    free(a);
	
    // Case 1: assigned at declaration
    int *p = 0;
    
    // Case 2: assigned later
    int *q;
    q = 0;
    
    //@ assert p == q;
    
    // Case 3:
    fractionPtr r = 0;
    
    // Case 4:
    fractionPtr s;
    s = 0;
    
    //@ assert r == s;
    
    if (p != 0) {
        //@ assert \false;
    }

    return 0;
}
