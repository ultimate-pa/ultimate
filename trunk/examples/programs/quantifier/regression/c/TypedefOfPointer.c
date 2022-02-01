//#Safe
/*
 * Date: October 2013
 * Author: heizmann@informatik.uni-freiburg.de
 * 
 */

#include <stdlib.h>

//int* intPointer;
typedef int* intPointer;

int main() {
    int *p = malloc(sizeof(int));
	intPointer q;
	q = p;
	free(p);
    return 0;
}
