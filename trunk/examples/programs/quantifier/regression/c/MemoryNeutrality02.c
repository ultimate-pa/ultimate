//#Unsafe
/*
 * Unsafe. The main function is not memory-neutral.
 * Date: 2025-10-04
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
    return 0;
}
