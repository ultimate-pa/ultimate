//#Unsafe
// Unsafe because n can be one, hence access to a[1] is invalid
// Author: heizmann@informatik.uni-freiburg.de
// Date: 27.7.2012


void procWithArray(int n);

void procWithArray(int n) {
	if (n > 0) {
		int a[n];
		a[1] = 0;
	}
}
