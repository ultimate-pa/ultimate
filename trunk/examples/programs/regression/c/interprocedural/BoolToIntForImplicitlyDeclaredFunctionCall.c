//#Unsafe
// Before b01feb9d0cc2fb3cb75c3c70105f47a99aab1366 we forgot to convert the 
// Boolean argument into an int argument
// Author: heizmann@informatik.uni-freiburg.de
// Date: 2018-10-23


int main(void) {
	int x;
	int res = someImplicitlyDeclaredFunction(x == 3);
	// the following assert should fail because we assume that
	// an implicitly declared function can return any value
	//@ assert res == 0;
}
