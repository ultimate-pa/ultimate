//#Safe
/* 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2016-07-17
 * 
 */


#include <stdio.h>
#include <float.h>
#include <math.h>

int main() {
	float f = 0.1;
// 	printf("%f", f); 
// 	printf("%d", signbit(f)); 
	if (signbit(f) != 0) {
		//@ assert \false;
	}

}
