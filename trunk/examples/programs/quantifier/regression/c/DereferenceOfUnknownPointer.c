//#Unsafe
/*
 * Date: September 2013
 * Author: heizmann@informtik.uni-freiburg.de
 * 
 */

#include <stdlib.h>

int main() {
    int *p;
    p = (int *) 4;
    *p = 3;
}
