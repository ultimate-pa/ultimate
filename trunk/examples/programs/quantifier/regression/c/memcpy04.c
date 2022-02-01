//#Unsafe
/* Check that invalid src is detected.
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
	free(src);
	void *res = memcpy(dst,src,2);
	free(dst);
	return 0;
}
