//#Safe
/* Bug: sizeOf the array is -4938268.
 * Minimized version of ldv-memsafety/memleaks_test23_1_true-valid-memsafety.i
 * 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2016-12-30
 * 
 */
#include <stdio.h>

int foo() {
    return 0;
}


int main(void) {
    int (*arrayOfFunctionPointers[1])() = { foo };
    int size1 = sizeof(arrayOfFunctionPointers);
    int *p;
    int size2 = sizeof(p);
    //@ assert size1 == size2;
    return 0;
}
