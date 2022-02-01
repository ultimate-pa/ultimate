//#Safe
/* Check e.g., that string is zero terminated.
 * 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2017-01-06
 * 
 */



int main(void) {
    char *string = "Newspeak";
    char secondLetter = string[1];
    char the_e_Letter = 'e';
    if (secondLetter != the_e_Letter) {
        //@ assert \false;
    }
    char term = string[8];
    char zero = '\0';
    if (term != zero) {
        //@ assert \false;
    }
    return 0;
}
