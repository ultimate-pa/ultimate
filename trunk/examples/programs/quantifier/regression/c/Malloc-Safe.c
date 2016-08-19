//#Safe
/*
 * Opposed to Malloc-Unsafe.c this is safe because the procedure in which memory 
 * is allocated but not freed is not the main procedure.
 * Date: September 2013
 * Author: heizmann@informatik.uni-freiburg.de
 * 
 */

#include <stdlib.h>

int nonMain() {
	// check also that conversion does not crash
	long long size = sizeof(int);
    int *p = malloc(size);
    return 0;
}
