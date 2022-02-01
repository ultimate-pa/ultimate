//#Safe
/* Reveals bug that prerunner is ignoring function pointers.
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2016-02-29 (leap day)
 * 
 */

#include <stdlib.h>
#include <stdio.h>

int inc(int x) {
	return x + 1;
}

int dec(int x) {
	return x - 1;
}

int main() {
	int (* func)(int);
	int (*(* p))(int) = &func;
	func = &inc;
 	int y = 0;
 	y = (*p)(y);
 	printf("%d\n",y);
	//@ assert y == 1;
}
