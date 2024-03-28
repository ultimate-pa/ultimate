// #Termination
/* 
 * Date: 2014-07-30 
 * Author: heizmann@informatik.uni-freiburg.de
 */

int main(void) {
	int x,y;
	y = 0;
	while (x > 0) {
		x = (x & y);
	}
}