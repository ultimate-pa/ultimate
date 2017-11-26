//#Safe
/* 
 * Just like Strings02.c, but with a string literal that is short enough not to
 * trigger our overapproximation of long string literals.
 * 
 * Author: nutz@informatik.uni-freiburg.de
 * Date: 2017-11-23
 * 
 */



int main(void) {
    char *string = "News";
    char secondLetter = string[1];
    char the_e_Letter = 'e';
    if (secondLetter != the_e_Letter) {
        //@ assert \false;
    }
    char term = string[4];
    char zero = '\0';
    if (term != zero) {
        //@ assert \false;
    }
    return 0;
}
