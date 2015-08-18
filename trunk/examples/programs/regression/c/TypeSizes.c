//#Safe
/* 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 17.08.2015
 * 
 * TODO Tests for all rules specified in 6.3.1.1 of C11
 */

int main() {
	if (!(sizeof(char) <= sizeof(short))) {
		//@assert \false;
	}
}
