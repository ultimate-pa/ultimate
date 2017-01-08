//#Unsafe
/*
 * 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2017-01-07
 * 
 */

#include <string.h>

int main(void) {
    char *string1 = "fakenews";
    char *string2 = 0;
    int r = strcmp(string1,string2);
    return 0;
}
