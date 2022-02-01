//#Safe
/* Check that not more values than specified are copied.
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
	char *dstPlusTwo = dst+2;
	*dstPlusTwo = 23;
	void *res = memcpy(dst,src,2);
	char dst_third = *(dstPlusTwo);
	printf("%d\n",dst_third);
	//@ assert dst_third == 23;
	free(src);
	free(dst);
	return 0;
}
