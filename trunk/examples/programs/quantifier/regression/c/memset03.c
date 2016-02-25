//#Unsafe
/*
 * Check that write over allocated area is detected.
 * Date: 2016-02-23
 * Author: heizmann@informtik.uni-freiburg.de
 * 
 */

#include <stdlib.h>
#include <string.h>
#include <stdio.h>

int main() {
	unsigned char *p = malloc(3*sizeof(char));
	char *s = memset(p+1, -1, 3*sizeof(char));
	free(p);
	return 0;
}
