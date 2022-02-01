//#Unsafe
/* 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2015-09-08
 * 
 */

#include <stdlib.h>

int main(void) {
	int a[2] = { 23, 42 };
	int b[2] = { 23, 42 };
	int *p = &a[0];
	int *q = &b[0];
	int d = p - q;
	return 0;
}
