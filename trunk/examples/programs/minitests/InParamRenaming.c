//#Safe
// Author: lindenmm@informatik.uni-freiburg.de
// Date: 16.08.2012
int method1(int, int);

/*@
 @ requires named1 > 0;
 @*/
int method2(int, int named1);

int method1(int a, int b) {
	if (a > b)
		return a - b;
	else
		return b - a;
}

int method2(int c, int d) {
	return c + d + method1(c, d);
}

int main() {
	int k = method2(10,11);
	//@ assert k == 22;
}
