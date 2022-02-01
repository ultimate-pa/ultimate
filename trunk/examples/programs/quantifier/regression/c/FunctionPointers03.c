//#Safe
/* C11 6.3.2.1.4 says that function designator is expression that has 
 * function type. However, in most cases it is converted to a pointer and hence
 * the comparison &inc != inc is legal.
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2015-09-04
 * 
 */

#include <stdlib.h>

int inc(int x) {
	return x + 1;
}

int main() {
	if (&inc != inc) {
		//@ assert \false;
	}
	int y = 23;
	int (* func)(int);
	func = inc;
	y = func(y);
	//@ assert y == 24;
}
