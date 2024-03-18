//#Safe
/* 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2016-07-11
 * 
 */


#include <stdio.h>
#include <float.h>
#include <math.h>

extern int __isinfl (long double __value) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));

int main() {
	long double ld = 0.1/0.0;
// 	printf("%LF", ld); 
// 	printf("%d", __isinfl(ld)); 
	if (!__isinfl(ld)) {
		//@ assert \false;
	}

}
