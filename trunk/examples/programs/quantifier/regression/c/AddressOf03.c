//#Safe
/* 
 * Date: 2016-02-27
 * Author: heizmann@informatik.uni-freiburg.de
 * 
 */
#include <stdlib.h>

struct container {
	int index;
};

int nonMain() {
	struct container *p = malloc(sizeof(struct container));
	p->index = 0;
	int arr[3];
	int *adr = & arr[p->index];
	if (arr[0] != *adr) {
		//@ assert \false;
	}
}
