//#Safe
// Author: heizmann@informatik.uni-freiburg.de
// Date: 2015-09-19

void main();

void main() {
	int i = 1;
	int a[++i][2];
	//@ assert i = 2;
}