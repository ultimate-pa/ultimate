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
	*src = 3;
	*(src+1) = 17;
	*(src+2) = 42;
	void *res;
	res = memcpy(dst,src,3);
	//@ assert dst == res;
	char third = *(src+2);
	printf("%d\n",third);
	//@ assert third == 42;
	free(src);
	free(dst);
	return 0;
}
