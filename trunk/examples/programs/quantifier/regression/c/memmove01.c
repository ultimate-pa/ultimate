//#Safe
/* Check that we allow overlapping pointers and copy as expected. 
 * Date: 2017-11-27
 * Author: Dietsch
 * 
 */

#include <stdlib.h>
#include <string.h>
#include <stdio.h>

int nonMain() {
	char *src = malloc(3*sizeof(char));
	char *dst = (*src+1);
    *src = 'a';
    *(src+1) = 'b';
	void *res = memmove(dst,src,2);
    if(*src != 'a'){
        //@assert \false;
    }
    if(*dst != 'a'){
        //@assert \false;
    }
	free(src);
	return 0;
}
