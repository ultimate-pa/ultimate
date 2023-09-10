//#Safe
// Author: heizmann@informatik.uni-freiburg.de
// Date: 2022-11-06
// 
// Our WitnessPrinter throws a NullPointerException.
// The problem seems to be that the Boogie expression
// that represent the conditions of the while loop do
// point to an AST node of the C program but to `null`
// instead.

int main() {
	int i = 5;
	int x = 0;
	for (;;) {
		i = i + x;
		//@ assert i == 5;
	}
}
