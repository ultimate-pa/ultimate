//#Safe
/* Check that there is no memory leak.
 * Date: 2016-02-22
 * Author: heizmann@informatik.uni-freiburg.de
 * 
 */

#include <stdlib.h>
#include <string.h>
#include <stdio.h>

int main() {
	char *src = malloc(3*sizeof(char));
	char *dst = malloc(3*sizeof(char));
	void *res = memcpy(dst+1,src,2);
	//@ assert res == dst+1;
	free(src);
	free(dst);
	return 0;
}
