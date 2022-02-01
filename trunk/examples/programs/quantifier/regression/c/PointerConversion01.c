//#Unsafe
/* 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2016-02-29 (leap day)
 * 
 */

#include <stdlib.h>
#include <stdio.h>

int main() {
	int *p = malloc(sizeof(int));
	long value = (long) p;
	//@ assert value != 1;
	free(p);

}
