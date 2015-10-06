/*
 * Date: 2013-12-20
 * Author: leike@informatik.uni-freiburg.de
 *
 * Difficult example for non-termination
 *
 * y = x^log_2(3)
 */

int main()
{
	int x = 1;
	int y = 1;
	while (x >= 0) {
		x = 2*x;
		y = 3*y;
	}
	return 0;
}

