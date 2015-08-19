/*
 * Date: October 2013
 * Author: Christian Schilling
 * 
 * 'NULL' is not recognized.
 */

#include <stdlib.h>

int main() {
    int* p = NULL;
	int* q = malloc(sizeof(int));
	if (p == q) {
		//@ assert \false;
	}
	free(q);
    return 0;
}
