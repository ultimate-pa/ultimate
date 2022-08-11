//#Safe
/*
 * Here we have an array of pointers to function pointers.
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2022-02-25
 * 
 */
#include <stdio.h>

int foo() {
    return 23;
}


int main(void) {
    int (*p)() = foo;
    int (**q)() = &p;
    int (**arrayOfFunctionPointers[1])() = { q };
    int res = (*arrayOfFunctionPointers[0])();
    printf("%d\n", res);
    //@ assert res == 23;
    return 0;
}
