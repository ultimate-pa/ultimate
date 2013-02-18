//#mUnsafe
// Author: heizmann@informatik.uni-freiburg.de
// Date: 27.7.2012

/*@ requires n > 1048;
  @*/
void procWithArray(int n);

void procWithArray(int n) {
	int a[n];
	int x;
	x = a[23];
	//@assert x == 0;
}
