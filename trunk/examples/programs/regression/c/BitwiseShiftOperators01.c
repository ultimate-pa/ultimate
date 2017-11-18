//#Safe
/* 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2017-11-18
 * 
 */


int main(void) {
	int a = 5;
	int b = a << 4;
	if (b != 80) {
		//@ assert \false;
	}
	
	// 2^31+1
	unsigned int c = 2147483649;
	unsigned int d = c << 1;
	if (d != 2) {
		//@ assert \false;
	}
	
	return 0;
}
