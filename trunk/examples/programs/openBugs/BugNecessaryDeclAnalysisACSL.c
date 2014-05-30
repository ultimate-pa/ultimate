/* #Safe
 * 
 * Problem: The analysis for neccesary declarations does not check for
 * variable usage in ACSL.
 * 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 30.5.2014
 * 
 */

int g;

int main() {
        //@ assert g == 0;
}
