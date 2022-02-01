//#Safe
/*
 * Check that values are written.
 * Date: 2016-02-23
 * Author: heizmann@informatik.uni-freiburg.de
 * 
 */

#include <stdlib.h>
#include <string.h>
#include <stdio.h>

int main() {
	unsigned char *p = malloc(3*sizeof(char));
	char *s = memset(p, -1, 3*sizeof(char));
	//@ assert s == p;
	int snd = *(p+2);
	printf("%d\n",snd);
	//@ assert snd == 255;
	free(p);
	return 0;
}
