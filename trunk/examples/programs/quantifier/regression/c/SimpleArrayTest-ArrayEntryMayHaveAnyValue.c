//#Unsafe
// Author: heizmann@informatik.uni-freiburg.de
// Date: 27.7.2012

void procWithArray(int n);

void procWithArray(int n) {
	if (n > 1048) {
		int a[n];
		int x;
		x = a[23];
		//@assert x == 0;
	}
}
