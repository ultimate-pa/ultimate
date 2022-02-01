//#Safe
/* Bug in r15168. Array a is considered "off heap", although its adress is 
 * taken in the assignment "int *p = a;"
 * 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2015-09-06
 * 
 */

#include <stdlib.h>

int main(void) {
	int a[2] = { 23, 42 };
	int *p = a;
	p++;
	int x = *p;
	//@ assert x == 42;
	return 0;
}
