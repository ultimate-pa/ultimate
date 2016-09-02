/*
 * Date: 2014-06-22
 * Author: heizmann@informatik.uni-freiburg.de
 */
#include <stdlib.h>

int main() {
	int* x0 = alloca(sizeof(int));
	int* x1 = alloca(sizeof(int));
	int* x2 = alloca(sizeof(int));
	int* x3 = alloca(sizeof(int));
	*x0 = 0;
	*x1 = 0;
	*x2 = 0;
	*x3 = 0;
	while ( *x3 == 0 ) {
		if (*x0 == 0) {
			*x0 = 1;
		} else {
			*x0 = 0;
			if (*x1 == 0) {
				*x1 = 1;
			} else {
				*x1 = 0;
				if (*x2 == 0) {
					*x2 = 1;
				} else {
					*x2 = 0;
					*x3 = 1;
				}
			}
		}
	}
	return 0;
}