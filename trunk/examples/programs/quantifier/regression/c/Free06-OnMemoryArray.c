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

int g;

int main() {
    free(&g);
    return 0;
}
