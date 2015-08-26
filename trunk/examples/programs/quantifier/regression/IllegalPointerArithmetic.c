//#Unsafe
/* 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2015-08-27
 * 
 * Pointer arithmetic here is undefined since 
 * p is void pointer and void is an incomplete type.
 */

#include <stdio.h>

int main() {
	void* p = 0;
	p++;
	return 0;
}
