//#Unsafe
/*
 * This is an example for a non-obvious bug in a C program.
 * Assume that array arr is some cyclic buffer of size 256.
 * In each iteration we write two new values in the buffer.
 * Since the current position pos is an unsigned char one might expect that
 * (pos + 1) is always between 0 and 255. However, because of the "usual
 * arithmetic conversions" the expression pos + 1 has type int and can be
 * evaluated to 256.
 * 
 * Date: 2016-02-11
 * Author: heizmann@informatik.uni-freiburg.de
 * 
 */
#include <stdlib.h>

extern unsigned char getInitialPosition();
extern int getNextValue();

int main() {
    unsigned char pos = getInitialPosition();
    int arr[256];
    while(1) {
        arr[pos] = getNextValue();
        arr[pos + 1] = getNextValue();
        pos += 2;
    }
    return 0;
}

