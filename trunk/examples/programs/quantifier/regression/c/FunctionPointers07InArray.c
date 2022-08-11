//#Safe
/*
 * We fail to determine the size of the array,
 * although the size is given by the initializer.
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2022-02-25
 * 
 */
#include <stdio.h>

int foo() {
    return 23;
}


int main(void) {
    int (*arrayOfFunctionPointers[])() = { foo };
    int res = arrayOfFunctionPointers[0]();
    printf("%d\n", res);
    //@ assert res == 23;
    return 0;
}
