//#Safe
/* 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2015-10-10
 */


int main(void) {
	union myUnion {
		int fst[3];
		int snd;
	} var;
	
	if (sizeof(var) != sizeof(int)*3) {
		//@assert \false;
	}
	return 0;
}
