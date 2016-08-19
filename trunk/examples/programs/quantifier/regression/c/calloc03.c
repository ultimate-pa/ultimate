//#Unsafe
/*
 * Check that memory leak is detected.
 * Date: 2016-02-24
 * Author: heizmann@informatik.uni-freiburg.de
 * 
 */

#include <stdlib.h>
#include <stdio.h>

int main() {
	int *p = calloc(3, sizeof(int));
	*p = 42;
	return 0;
}
