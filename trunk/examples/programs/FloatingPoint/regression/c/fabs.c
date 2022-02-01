//#Safe
/* 
 * Author: heizmann@informatik.uni-freiburg.de, Julian Löffler
 * Date: 2018-09-20
 * 
 */

#include <stdio.h>
#include <float.h>
#include <math.h>


int main() {
	double x = fabs(-4.0);
	if (x != 4.0) {
		//@ assert \false;
	}
	
	double y = 0.0 / 0.0; // NAN
	double res = fabs(y);
	// y is NAN, fabs(y) should be NAN, Error should not be reachable.
	if (res > 1) {
		//@ assert \false;
	}
}
