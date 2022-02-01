//#Safe
/* 
 * Pointer arithmetic where one operand is a string literal.
 * 
 * Similar operations occur in many busybox examples from the SV-COMP. E.g.,
 * test-incomplete_false-unreach-call_true-no-overflow_true-valid-memsafety.i
 * 
 * Currently we get the following error message. 
 * UnsupportedOperationException: non-standard case of pointer arithmetic
 * 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2017-11-26
 * 
 */
#include <stdlib.h>
#include <stdio.h>


int main(void) {
    char *string = "Lorien" + 1UL;
    char secondLetter = string[0];
	printf("%c\n",secondLetter);
    char the_o_Letter = 'o';
    if (secondLetter != the_o_Letter) {
        //@ assert \false;
    }
    return 0;
}
