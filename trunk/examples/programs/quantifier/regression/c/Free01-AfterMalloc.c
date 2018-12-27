//#Safe
/*
 * Date: 2018-12-26
 * Author: heizmann@informatik.uni-freiburg.de
 * 
 */

#include <stdlib.h>

int main() {
    int *p = malloc(sizeof(int));
    free(p);
    return 0;
}
