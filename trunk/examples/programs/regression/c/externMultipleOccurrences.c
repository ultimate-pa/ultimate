//#Safe
// Author: heizmann@informatik.uni-freiburg.de
// Date: 2022-11-10
//
// It looks like it is allowed to have several declarations
// of a global variable. Expecially if they are `extern`.

#include <stdio.h>

extern int myVar;

int myVar = 42;

extern int myVar;

int main() {
	//@ assert myVar == 42;
	printf("%d\n",myVar);
	return 0;
}

extern int myVar;
