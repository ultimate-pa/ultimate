//#Safe
/* 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2016-08-09
 * 
 */

int main(void) {
	float f = 1.0;
	f++;
	//@ assert f == 2.0;
	return 0;
}
