//#Safe
// Author: heizmann@informatik.uni-freiburg.de
// Date: 2016-02-26


int main() {
	unsigned char a[2] = { -1, -1 };
	int x = a[0];
	if (x != 255) {
		//@ assert \false;
	}
}