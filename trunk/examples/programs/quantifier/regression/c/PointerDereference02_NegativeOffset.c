//#Unsafe
/* 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2016-12-17
 * 
 */

#include <stdlib.h>

int main() {
    long long *p = malloc(sizeof(long long));
    p--;
    int x = *p;
    return 0;
}
