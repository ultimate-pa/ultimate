//#Safe
/* 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2016-07-11
 * 
 */

#include <stdio.h>
#include <float.h>
#include <math.h>


extern double sqrt (double __x) __attribute__ ((__nothrow__ , __leaf__));

int main() {
	double x = sqrt(4.0);
	if (x != 2.0) {
		//@ assert \false;
	}
}
