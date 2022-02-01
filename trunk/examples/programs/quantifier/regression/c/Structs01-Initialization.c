//#Safe
// Values in initializer are converted
// Author: heizmann@informatik.uni-freiburg.de
// Date: 2016-02-27

#include <stdio.h>

struct charPair {
	unsigned char fst;
	unsigned char snd;
};

int main() {
	struct charPair cp = { -1, 2 };
	int x = cp.fst;
	printf("%d\n",x);
	//@ assert x = 255;
}