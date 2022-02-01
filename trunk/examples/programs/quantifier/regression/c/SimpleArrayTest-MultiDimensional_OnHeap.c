//#Safe
// Author: heizmann@informatik.uni-freiburg.de
// Date: 2015-09-21

#include <stdio.h>

int main(void) {
	int a[3][5][7];
	a[2][3][4] = 23;
	int *p = &(a[0][0][0]);
	int x = *(p + 2*5*7 + 3*7 + 4);
	printf("%d\n",x);
	if (x != 23) {
		//@ assert \false;
	}
}