//#Safe
/* Before dereferencing a function designator expression is converted to a
 * pointer. Hence e.g., ***inc is legal.
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2015-09-04
 * 
 */

#include <stdlib.h>

int inc(int x) {
	return x + 1;
}

int main() {
	if (&inc != ***inc) {
		//@ assert \false;
	}
	int y = 23;
	int (* func)(int);
	func = inc;
	y = (*(***(*func)))(y);
	//@ assert y == 24;
}
