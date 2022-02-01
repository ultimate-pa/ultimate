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

int main() {
	fraction* p = malloc(sizeof(fraction));
	p->num = 3;
	(*p).denom = 4;
	int a = p->denom;
	//@ assert a == 4;
	int b = (*p).num;
	//@ assert b == 3;
	free(p);
}
