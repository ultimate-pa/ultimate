//#Safe
// Author: heizmann@informatik.uni-freiburg.de
// Date: 2015-09-18


int main() {
	int a[3][4] = {
		{ 11, 12 },
		{ 21},
	};
	if (a[1][0] != 21) {
		//@ assert \false;
	}
	if (a[2][0] != 0) {
		//@ assert \false;
	}
}