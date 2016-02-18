//#Safe
// Author: heizmann@informatik.uni-freiburg.de
// Date: 2016-02-01

#include <stdio.h>

int main() {
	// prefix 0 defines octal representation
	if (023 == 19) {
		printf("assertion holds\n");
	} else {
		printf("assertion violated\n");
		//@ assert \false;
	}

	// prefixes 0x and 0X define hexadecimal representation
	if (0x23 == 35 && 0X23 == 35 ) {
		printf("assertion holds\n");
	} else {
		printf("assertion violated\n");
		//@ assert \false;
	}
	
	if (sizeof(int) == 4 && sizeof(long) > 4) {
		
		// prefixes 0x and 0X define hexadecimal representation
		if (0x23 == 35 && 0X23 == 35 ) {
			printf("assertion holds\n");
		} else {
			printf("assertion violated\n");
			//@ assert \false;
		}
		
		// 2147483648 has type long
		if (2147483648 > 2147483647) {
			printf("assertion holds\n");
		} else {
			printf("assertion violated\n");
			//@ assert \false;
		}
		
		// 2147483648u has type unsigned int
		if (2147483648u + 2147483648u == 0 ) {
			printf("assertion holds\n");
		} else {
			printf("assertion violated\n");
			//@ assert \false;
		}
		
		// 0x80000000 is 2^32
		if (0x80000000 == 2147483648u) {
			printf("assertion holds\n");
		} else {
			printf("assertion violated\n");
			//@ assert \false;
		}
		
		// 0x80000000 has type unsigned int
		if (0x80000000 + 0x80000000 == 0) {
			printf("assertion holds\n");
		} else {
			printf("assertion violated\n");
			//@ assert \false;
		}
	}
	
	return 0;
}
