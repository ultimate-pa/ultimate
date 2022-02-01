/*
 * author: nutz, 10.02.2014
 */

int foo() {
	return 3;
}

int main() {
	int x = 0;

	if (1 && x != foo()) {
		x = 9;
	}
	
	if (0 || x != foo()) {
		x = 89;
	}
}

