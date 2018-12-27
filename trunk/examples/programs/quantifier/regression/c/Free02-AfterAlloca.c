//#Unsafe
/*
 * Date: 2018-12-26
 * Author: heizmann@informatik.uni-freiburg.de
 * 
 * Before the introduction of the stack-heap barrier,
 * we returned an incorrect result on this example.
 * 
 */

#include <stdlib.h>

int main() {
    int *p = alloca(sizeof(int));
    free(p);
    return 0;
}
