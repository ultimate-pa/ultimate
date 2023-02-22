//#Unsafe

/*
 * Date: 2023-02-22
 * schuessf@informatik.uni-freiburg.de
 *
 */

#include <stdio.h>

int main(void) {
	int x = 0;
	char* string = "Long enough string to be overapproximated";
	printf("%s", string);
	int y = 1;
	//@ assert x == y;
}
