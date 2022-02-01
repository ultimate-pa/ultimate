//#Safe
/*
 * Date: October 2013
 * Author: heizmann@informatik.uni-freiburg.de
 * 
 */

#include <stdlib.h>

typedef struct {
	int num;
	int denom;
} fraction;

typedef struct {
      int color;
      fraction frac;
} colorWithFieldFraction;


int main() {
	colorWithFieldFraction* p = 
		malloc(sizeof(colorWithFieldFraction));
	p->frac.num = 23;
	int a = p->frac.num;
	//@ assert a == 23;
	int b = (*p).frac.num;
	//@ assert b == 23;
	free(p);
}
