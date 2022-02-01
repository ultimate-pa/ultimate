//#Unsafe
/*
 * Date: September 2013
 * Author: heizmann@informatik.uni-freiburg.de
 * 
 */

#include <stdlib.h>

int main() {
    int *p;
    p = (int *) 4;
    *p = 3;
}
