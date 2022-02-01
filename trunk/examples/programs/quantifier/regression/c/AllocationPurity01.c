//#Safe
/*
 * Safe, but the function doAlloc is not allocation pure.
 * Date: 2017-10-17
 * Author: heizmann@informatik.uni-freiburg.de
 * 
 */

#include <stdlib.h>

int *doAlloc() {
    int *p = malloc(sizeof(int));
    return p;
}

int main() {
    int *p = doAlloc();
    free(p);
    return 0;
}
