//#Unsafe
// Author: heizmann@informatik.uni-freiburg.de
// Date: 2015-08-11
//
// Program is not safe. No guarantee that there is a wraparound for booleans.
// E.g., with gcc on my machine the ouput of the last printf is 1.

#include <stdio.h>

int main(void) {
	_Bool x = 0;
	printf("%d\n",x);
	x++;
	printf("%d\n",x);
	x++;
	printf("%d\n",x);
	//@ assert x == 0;
}