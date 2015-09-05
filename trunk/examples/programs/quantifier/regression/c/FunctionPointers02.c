//#Safe
/* 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2015-08-30
 * 
 */

#include <stdlib.h>

int inc(int x) {
	return x + 1;
}

int dec(int x) {
	return x - 1;
}

int (*getFun(int x))(int) {
	if (x > 0) {
		return &inc;
	} else {
		return &dec;
	}
}

int main() {
	int y = 23;
	int (* func)(int);
	func = getFun(7);
	y = func(y);
	y = func(y);
	func = getFun(0);
	y = func(y);
	//@ assert y == 24;
}
