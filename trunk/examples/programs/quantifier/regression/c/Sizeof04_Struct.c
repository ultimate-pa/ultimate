//#Safe
/* 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2015-10-10
 */


int main(void) {
	struct myStruct {
		char fst[3];
		long snd;
	} var;
	
	if (sizeof(var) != sizeof(char)*3 + sizeof(long)) {
		//@assert \false;
	}
	return 0;
}
