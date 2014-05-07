//#Unsafe
/*
 * Date: September 2013
 * Author: heizmann@informtik.uni-freiburg.de
 * 
 */

#include <stdlib.h>

int nonMain() {
    int *p = malloc(sizeof(int));
    //// @assert *p == 0; //we cannot handle pointer dereferences in acsl yet
    if (*p != 0) {
	//@assert \false;
    }
    return 0;
}
