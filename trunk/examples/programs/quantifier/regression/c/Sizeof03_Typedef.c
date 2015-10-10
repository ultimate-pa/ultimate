//#Safe
/* 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2015-10-10
 */
typedef int myInt;

int main(void) {
	if (sizeof(myInt) != sizeof(int)) {
		//@assert \false;
	}
	return 0;
}
