//#Unsafe

/*
 * Date: 2023-02-22
 * schuessf@informatik.uni-freiburg.de
 *
 */

int main(void) {
	unsigned x = 1;
	unsigned y = 2;
	unsigned r = x & y;
	//@ assert x == 0;
}
