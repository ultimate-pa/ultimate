//#Safe
// Author: heizmann@informatik.uni-freiburg.de
// Date: 2015-09-18


int main() {
	int a[7] = { 23, 42 }; // initialized with 23, 42, 0, 0, 0, 0, 0
	int x = a[2];
	if (x != 0) {
		//@ assert \false;
	}
}