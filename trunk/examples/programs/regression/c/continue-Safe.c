//#Safe
/*
 * Date: November 2013
 * Author: Christian Schilling
 * 
 * 'continue' is not supported.
 */
int main() {
	int a;
	while (1) {
		if (a != 5) {
			continue;
		} else {
			//@ assert a == 5;
		}
	}
}
