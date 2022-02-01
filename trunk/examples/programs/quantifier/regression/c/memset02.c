//#Unsafe
/*
 * Check that invalid pointer base is detected.
 * Date: 2016-02-23
 * Author: heizmann@informatik.uni-freiburg.de
 * 
 */

#include <stdlib.h>
#include <string.h>
#include <stdio.h>

int main() {
	unsigned char *p = malloc(3*sizeof(char));
	unsigned char c = *p;
	free(p);
	char *s = memset(p, -1, 3*sizeof(char));
	return 0;
}
