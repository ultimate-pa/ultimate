//#Unsafe
/* Invalid pointer dereference 
 * 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2017-01-06
 * 
 */

int main(void) {
    char *string = "grimes";
    char not_a_letter = string[7];
    return 0;
}
