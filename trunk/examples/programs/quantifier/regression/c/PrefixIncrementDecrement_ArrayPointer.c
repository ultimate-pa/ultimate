//#Safe
/* Check that we handle increment/decrement of pointers correctly
 * if the pointer has an array type.
 * 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2017-11-30
 * 
 */

int nonMain(void) {
	int a[2][2] = {  
		{0, 1},
		{2, 3},
	};
	int (*p)[2] = &(a[0]);
	++p;
	int *pint = (int*) p;
	int x = *pint;
	//@ assert x == 2;
	
	int (*q)[2] = &(a[1]);
	--q;
	int *qint = (int*) q;
	int y = *qint;
	//@ assert y == 0;
	
	return 0;
}
