//#Safe
// Author: heizmann@informatik.uni-freiburg.de
// Date: 27.7.2012

void procWithArray();

void procWithArray() {
	int a[1];
	a[0] = 0;
	a[0]++;
	int x;
	x = a[0];
	//@ assert x == 1;
}
