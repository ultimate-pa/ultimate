//#Safe
/*
 * Date: September 2013
 * Author: heizmann@informatik.uni-freiburg.de
 * 
 */

#include <stdlib.h>

int main() {
    int *p = malloc(sizeof(int));
    int *q = malloc(sizeof(int));
    // @assert  p != q;
    free(p);
    free(q);
}
