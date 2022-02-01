/* #Safe
 * 
 * Test that global var g has been initialized.
 * TODO: More detailed explantation what kind of variable g is according to
 * C99 standard.
 * 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 28.3.2013
 * 
 */

int g;

int main() {
	if (g != 0) {
		//@ assert \false;
	}
}
