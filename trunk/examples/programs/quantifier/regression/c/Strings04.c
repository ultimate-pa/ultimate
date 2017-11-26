//#Safe
/* 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2017-11-17
 * 
 */

int main(void) {
	char myCharArray[7] = "Jamaica";
    char c = myCharArray[2];
    if (c != 'm') {
        //@ assert \false;
    }
    return 0;
}
