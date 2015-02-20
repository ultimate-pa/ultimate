//#Safe
/*
 * Date: 2014-06-22
 * Author: heizmann@informatik.uni-freiburg.de
 *
 */
#include <stdlib.h>

typedef struct {
	int zero;
	int one;
	int two;
	int three;
} fourBit;

int main() {
	fourBit* fb = malloc(sizeof(fourBit));
	fb->zero = 0;
	fb->one = 0;
	fb->two = 0;
	fb->three = 0;
	while ( fb->three == 0 ) {
		if (fb->zero == 0) {
			fb->zero = 1;
		} else {
			fb->zero = 0;
			if (fb->one == 0) {
				fb->one = 1;
			} else {
				fb->one = 0;
				if (fb->two == 0) {
					fb->two = 1;
				} else {
					fb->two = 0;
					fb->three = 1;
				}
			}
		}
	}
	int x3Value = fb->three;
	//@assert x3Value != 0;
	free(fb);
	return 0;
}