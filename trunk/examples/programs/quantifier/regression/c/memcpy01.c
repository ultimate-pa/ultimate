//#Safe
/* Check that values are copied and result is dst.
 * Date: 2016-02-22
 * Author: heizmann@informatik.uni-freiburg.de
 * 
 */

#include <stdlib.h>
#include <string.h>
#include <stdio.h>

int nonMain() {
	char *src = malloc(3*sizeof(char));
	char *dst = malloc(3*sizeof(char));
	*src = 17;
	*(src+1) = 42;
	void *res = memcpy(dst,src,2);
	//@ assert dst == res;
	char snd = *(src+1);
	printf("%d\n",snd);
	//@ assert snd == 42;
	free(src);
	free(dst);
	return 0;
}
