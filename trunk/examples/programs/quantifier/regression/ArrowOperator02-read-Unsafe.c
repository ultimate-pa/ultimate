//#Unsafe
/*
 * Date: October 2013
 * Author: Christian Schilling and heizmann@informatik.uni-freiburg.de
 * 
 */

#include <stdlib.h>

typedef struct {
	int num;
	int denom;
} fraction;

int main() {
	fraction* p;
	int a;
	a = p->num;
	int b;
	b = (*p).num;
	//@ assert a == 0 || b == 0;
}
