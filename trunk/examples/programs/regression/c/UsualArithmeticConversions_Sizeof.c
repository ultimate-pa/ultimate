//#Safe
/* 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2015-09-06
 * 
 */

#include <stdlib.h>

int main(void) {
	signed char schar = 1;
	signed short sshort = 1;
	signed int sint = 1;
	signed int uint = 1;
	signed long slong = 1;
	signed long long slonglong = 1;
	
	// integer promotion
	if (sizeof(schar + schar) != sizeof(int)) {
		//@ assert \false;
	}
	
	// integer promotion
	if (sizeof(sshort + schar) != sizeof(int)) {
		//@ assert \false;
	}
	
	// integer promotion
	if (sizeof(sshort + sshort) != sizeof(int)) {
		//@ assert \false;
	}
	
	// schar converted to unsigned int
	if (sizeof(schar + uint) != sizeof(unsigned int)) {
		//@ assert \false;
	}
	
	// int converted to long
	if (sizeof(sint + slong) != sizeof(long)) {
		//@ assert \false;
	}
	
	// int converted to long long
	if (sizeof(sint + slonglong) != sizeof(long long)) {
		//@ assert \false;
	}



	
	
	return 0;
}
