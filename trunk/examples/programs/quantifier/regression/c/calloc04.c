//#Safe
/*
 * Bug: modifies not transitive.
 * 
 * Date: 2016-05-15
 * Author: heizmann@informatik.uni-freiburg.de
 * 
 */

#include <stdlib.h>


void imon_probe() {
	calloc(1, sizeof(int));
}

int g;

void main(void) {
	g = 0;
	imon_probe();
}

