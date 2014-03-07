//#Safe
/*
 * Opposed to Malloc-Safe.c this is safe because the procedure in which memory 
 * is allocated but not freed is not the main procedure.
 * Date: September 2013
 * Author: heizmann@informtik.uni-freiburg.de
 * 
 */

#include <stdlib.h>

int nonMain() {
    int *p = malloc(sizeof(int));
    return 0;
}
