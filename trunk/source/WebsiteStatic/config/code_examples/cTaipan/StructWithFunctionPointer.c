//#Safe
/*
 * Date: 2016-02-11
 * Author: heizmann@informatik.uni-freiburg.de
 * 
 */
#include <stdlib.h>

extern short __VERIFIER_nondet_short();

struct valueWithFunction {
    int value;
	int (* func)(int);
};


int inc(int x) {
	return x + 1;
}

int dec(int x) {
	return x - 1;
}


int main() {
	short input = __VERIFIER_nondet_short();
	struct valueWithFunction data;
	data.value = input;
	if (input > 0) {
	    data.func = &inc;
	} else {
	    data.func = &dec;
	}
	data.value = data.func(data.value);
	//@ assert input > 0 ==> data.value > 0;
	//@ assert input <= 0 ==> data.value <= 0;
}

