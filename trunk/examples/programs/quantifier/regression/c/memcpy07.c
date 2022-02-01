//#Unsafe
/* Check that we do not read more memory than we have allocated.
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
	void *res = memcpy(dst,src+2,2);
	free(src);
	free(dst);
	return 0;
}
