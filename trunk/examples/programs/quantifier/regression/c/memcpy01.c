//#Safe
/*
 * Date: 2016-02-22
 * Author: heizmann@informtik.uni-freiburg.de
 * 
 */

#include <stdlib.h>
#include <string.h>
#include <stdio.h>

int main() {
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
