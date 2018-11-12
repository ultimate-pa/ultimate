/*
 * author: nutz, 05.02.2014
 */


int foo(void) {
	return 0;
}

int main() {

	int a = 1;

	while (a) {
		foo();
	}

	for (int n = 1; n < 10; ++n) {
		foo();
	}

	a = a ? 1 : 0;
}
