//#Safe
/* 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2015-08-27
 * 
 * Bug in r15080. We only check if base address is != 0 and hence incorrectly
 * set logicalNegation to 1.
 * Matthias: I have the feeling that something here is undefined behavior
 * but I have not found evidence for this claim in the C standard.
 */

#include <stdio.h>

int main() {
	char* p = 0;
	p++;
	printf("p: %p\n", p);
	int logicalNegation = !p;
	printf("logicalNegation: %d\n", logicalNegation);
	//@ assert logicalNegation == 0;
	return 0;
}
