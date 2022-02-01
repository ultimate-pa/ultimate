//#Safe
/* Bug in r15195. Array a is considered "off heap", although its adress is 
 * taken at the cast "(int *) a"
 * 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2015-09-06
 * 
 */

#include <stdlib.h>

int main(void) {
	int a[2] = { 23, 42 };
	int *p = (int *) a;
	p++;
	int x = *p;
	//@ assert x == 42;
	return 0;
}
