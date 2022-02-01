//#Safe
/*
 * Date: September 2013
 * Author: heizmann@informatik.uni-freiburg.de
 * 
 */

#include <stdlib.h>

int main() {
    long long *p = malloc(sizeof(long long));
    *p = 3;
    free(p);
    return 0;
}
