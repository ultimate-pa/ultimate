//#Unsafe
/*
 * Minimal example for reproducing a bug in my implementation of
 * the Hoenicke-Lindenmann memory model with 1byte resolution.
 * 
 * The combination of g's initialization and the write access
 * g = 1337 was equivalent to 'assume false'.
 * 
 * Date: 2019-11-26
 * Author: heizmann@informatik.uni-freiburg.de
 * 
 * 
 */

#include <stdlib.h>

int g;

int main() {
    *(&g) = 1337;
    //@ assert \false;
    return 0;
}
