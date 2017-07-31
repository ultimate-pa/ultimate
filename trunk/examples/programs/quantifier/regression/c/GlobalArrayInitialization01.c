//#Safe
/*  
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2017-06-07
 * 
 */
#include <stdio.h>

int a[10];

int main(void) {
    if (*(a+8) != 0) {
        printf("false");
        //@ assert \false;
    }
    return 0;
}
