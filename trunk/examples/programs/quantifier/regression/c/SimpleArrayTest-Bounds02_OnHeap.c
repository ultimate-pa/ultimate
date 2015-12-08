//#Unsafe
// Author: heizmann@informatik.uni-freiburg.de
// Date: 2015-09-19

int main(void);

int main(void) {
	int a[2] = { 23, 42 };
	// effect of the following seemingly useless line is that in our
	// translation array a will be "on-heap"
	int *p = &a[0];
	int x = a[2];
}