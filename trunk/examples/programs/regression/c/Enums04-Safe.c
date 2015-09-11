//#Safe
// Author: heizmann@informatik.uni-freiburg.de
// Date: 2015-08-11
// Assign enum element to int
// Obtained from Markus Lindenmann's enum example.

#include <stdio.h>


enum e_tag {
	a, b, c, d = 20, e, f, g = 20, h
} var;

int main() {
	enum e_tag y;
	y = f;
	int x = f;
	printf("%d\n",x);
	//@ assert x == 22;
}
