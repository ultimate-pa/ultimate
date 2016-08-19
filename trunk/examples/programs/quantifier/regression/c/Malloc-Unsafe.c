//#Unsafe
/*
 * Opposed to Malloc-Safe.c this is unsafe because not all memory allocated in
 * the main procedure is freed.
 * Date: September 2013
 * Author: heizmann@informatik.uni-freiburg.de
 * 
 */

#include <stdlib.h>

int main() {
    int *p = malloc(sizeof(int));
    return 0;
}
