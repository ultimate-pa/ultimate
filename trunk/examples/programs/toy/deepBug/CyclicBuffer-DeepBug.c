//#Unsafe
/*
 * Modification of the CyclicBuffer.c example where we need more than
 * 100 loop unfoldings until we reach the bug.
 * (Because of the "usual arithmetic conversions" the expression pos + 1 has 
 * type int and can be evaluated to 256.)
 * 
 * Date: 2016-07-22
 * Author: heizmann@informatik.uni-freiburg.de
 * 
 */
#include <stdlib.h>

extern unsigned char getInitialPosition();
extern int getNextValue();

int main() {
    unsigned char pos = getInitialPosition() % 2 + 1;
    int a[256];
    while(1) {
        a[pos] = getNextValue();
        a[pos + 1] = getNextValue();
        pos += 2;
    }
    return 0;
}

