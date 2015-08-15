//#Safe
// Author: heizmann@informatik.uni-freiburg.de
// Date: 2015-08-13

int test(int a, int b, _Bool c, _Bool d, int e, int f);

int test(int a, int b, _Bool c, _Bool d, int e, int f) {
	if (d) {
		return 0;
	} else {
		return -1;
	}
}

int main() {
	int result = test(1, 2, 0, 23, 5, 6);
	//@assert result == 0;
	return 0;
}
