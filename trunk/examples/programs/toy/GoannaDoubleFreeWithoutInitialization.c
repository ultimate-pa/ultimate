//#Safe
/*
 * Variant of the GoannaDoubleFree example where x is not initialized.
 * In addition we use an if-then-else to ensure that p is always deallocated
 * and hence there is no memory leak.
 * 
 * Date: September 2013
 * Author: heizmann@informatik.uni-freiburg.de
 * 
 */
#include <stdlib.h>

int main() {
    int x, *a;
    int *p = malloc(sizeof(int));
    if (x > 0) {
    	while ( x > 0 ) {
    		a = p;
    		if (x == 1) {
    			free(p);
    		}
    		x--;
    	}
    } else {
    	free(p);
    }
    return 0;
}
