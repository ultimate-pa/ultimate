//#Unsafe
/* Check that we detect overlapping pointers and refuse to copy.
 * Date: 2017-11-27
 * Author: Dietsch
 * 
 */

#include <stdlib.h>
#include <string.h>
#include <stdio.h>

int nonMain() {
	char *src = malloc(3*sizeof(char));
	char *dst = src;
	void *res = memcpy(dst,src,2);
	free(src);
	return 0;
}
