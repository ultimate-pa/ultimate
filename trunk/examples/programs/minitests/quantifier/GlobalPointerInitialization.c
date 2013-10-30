//#iSafe
/*
 * Global variable (without further modifiers - TODO check details in C99 
 * standard) is initialized with 0.
 * Date: October 2013
 * Author: heizmann@informtik.uni-freiburg.de
 * 
 */

int i;
int *p;

int main() {
	if (p != 0) {
	  //@ assert \false;
	}
}
