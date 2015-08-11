//#Safe
// Author: heizmann@informatik.uni-freiburg.de
// Date: 2015-08-11
// Obtained from Markus Lindenmann's enum example.

#include <stdio.h>


enum e_tag {
	a, b, c, d = 20, e, f, g = 20, h
} var;

int main() {
	int x = e;
	printf("%d\n",x);
	//@ assert a == 0;
	//@ assert b == 1;
	//@ assert c == 2;
	//@ assert d == 20;
	//@ assert e == 21;
	//@ assert f == 22;
	//@ assert g == 20;
	//@ assert h == 21;
}