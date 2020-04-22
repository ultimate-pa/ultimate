//#Safe
/* 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2016-08-09
 * 
 */

int main(void) {
	float f = 1.0f;
	f++;
	//@ assert f == 2.0f;
	return 0;
}
