//#Safe
/*
 * Date: 2016-02-21
 * Author: heizmann@informatik.uni-freiburg.de
 * 
 */

#include <stdlib.h>

struct myStruct {
	_Bool aBool;
	char aChar;
	short aShort;
	int anInt;
	long aLong;
	long long aLongLong;
	void *aPointer;
};


int main() {
	struct myStruct *p = malloc(sizeof(struct myStruct));
	p->aBool = 1;
	p->aChar = 17;
	p->aShort = 23;
	p->anInt = 42;
	p->aLong = 62L;
	p->aLongLong = 99LL;
	p->aPointer = 0;
	_Bool resBool = p->aBool;
	//@ assert resBool == 1;
	int resInt = p->anInt;
	//@ assert resInt == 42;
	free(p);
	return 0;
}
