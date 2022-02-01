//#Safe
/* 
 * Support for "universal character names" according to 
 * 6.4.3 of C11.
 * 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2018-03-11
 * 
 */
#include <stdio.h>
#include <uchar.h>

typedef short unsigned int char16_t;
typedef unsigned int char32_t;

int main(void) {
    char16_t c16 = u'\u00F6';
    printf("%d\n",c16);
    if (c16 != 246) {
        //@ assert \false;
    }
    char32_t c32 = U'\U0010FFFF';
    if (c32 != 1114111) {
        //@ assert \false;
    }
    printf("%d\n",c32);
}
