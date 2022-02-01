//#Safe
/* 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2016-12-18
 * 
 */

#include <stdlib.h>

int main() {
    int *p = 0;
    free(p);
    return 0;
}
