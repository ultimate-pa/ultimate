//#Unsafe
/*
 * Date: September 2013
 * Author: heizmann@informatik.uni-freiburg.de
 * 
 */

#include <stdlib.h>

int main() {
    int *p = malloc(sizeof(int));
    free(p);
    *p = 3;
}
