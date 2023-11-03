//#Safe
/*
 * Test for function pointers in array.
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2022-02-25
 * 
 */
#include <stdio.h>

int foo() {
    return 23;
}


int main(void) {
    int (*arrayOfFunctionPointers[1])() = { foo };
    int res = arrayOfFunctionPointers[0]();
    printf("%d\n", res);
    //@ assert res == 23;
    return 0;
}
