//#Safe
/* 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2016-07-17
 * 
 */


#include <stdio.h>
#include <float.h>
#include <math.h>

extern int __finitef (float __value) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));

int main() {
	float f = 0.1;
// 	printf("%f", f); 
// 	printf("%d", __finitef(f)); 
	if (!__finitef(f)) {
		//@ assert \false;
	}

}
