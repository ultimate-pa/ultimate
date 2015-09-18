//#Safe
// Author: lindenmm@informatik.uni-freiburg.de
// Date: 16.08.2012

int main();
int bar(int i);

int main(void) {
	bar(3);
}

int bar(int i) {
	int x = 1;
	int test;
	switch (i) {
		case 0:
			int k;
			return 1;
		case 1:
		case 2:
		case 3:
			x += 10;
			//@ assert x == 11;
		case 4:
			x += 1;
			k = 1;
			return x + 1;
		case 5:
			break;
		default:
			return 0;
	}

	x = 0;

	switch (i) {
		default:
		case 0:
		case 1:
			x += 10;
		case 4:
			x += 1;
			return x + 1;
		case 5:
			break;
		}
}
