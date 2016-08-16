//#Safe
/*
 * Variant of the GoannaDoubleFree example where we have one million loop
 * iterations. 
 * Using "ForwardPredicates" we fail to find a suitable loop invariant, using
 * "BackwardPredicates we succeed.
 * 
 * Date: 2015-04-02
 * Author: heizmann@informatik.uni-freiburg.de
 * 
 */
#include <stdlib.h>

int main() {
    int x, *a;
    int *p = malloc(sizeof(int));
    for (x = 1000000; x > 0; x--) {
        a = p;
        if (x == 1) {
            free(p);
        }
    }
    return 0;
}
