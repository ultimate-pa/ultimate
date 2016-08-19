//#Safe
/* Dereferencing p succeeds because the "data storage" x is allocated
 * Date: September 2013
 * Author: heizmann@informatik.uni-freiburg.de
 * 
 */

int nonMain() {
	int x;
	int *p = &x;
	int a = *p;
	//@ assert a == x;
}
