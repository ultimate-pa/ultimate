//#Unsafe
/* Invalid pointer dereference
 * Pointer arithmetic legal, one after allocated area.
 * Using it in strlen not legal.
 * 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2017-01-07
 * 
 */

#include <string.h>

int main(void) {
    char *string = "fs";
    string = string + 3;
    int l = strlen(string);
    return 0;
}
