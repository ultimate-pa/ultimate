//#Safe

/*
 * Date: 2023-02-22
 * schuessf@informatik.uni-freiburg.de
 *
 */

int main(void) {
	unsigned x, y, z;
	y = 1;
	z = 2;
	x = y & z;
	y = x;
	//@ assert y == 0;
}
