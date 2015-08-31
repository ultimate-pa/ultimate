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

int main() {
	int y = 23;
	int (* func)(int);
	func = &inc;
	y = func(y);
	y = func(y);
	func = &dec;
	y = func(y);
	//@ assert y == 24;
}
