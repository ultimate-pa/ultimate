//#Safe
/* 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2015-10-10
 */


int main(void) {
	if (sizeof(int*) != sizeof(void*)) {
		//@assert \false;
	}
	
	long long *p;
	if (sizeof(p) != sizeof(char*)) {
		//@assert \false;
	}
	
	return 0;
}
