// Bug: ArrayOutOfBounds is only detected if somewhere in the code the address
// of a is read.
// Author: heizmann@informatik.uni-freiburg.de
// Date: 27.7.2014


int main();

int main() {
	int a[1];
	a[23] = 0;
	// out tool gives the correct answer if we adde the following line
	// int *p = &a;
}
