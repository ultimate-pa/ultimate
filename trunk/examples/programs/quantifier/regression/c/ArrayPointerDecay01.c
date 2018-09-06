//#Safe
/*
 * Date: 2017-09-05
 * Author: heizmann@informatik.uni-freiburg.de
 * 
 */

int a[1];
int main(void)
{
	a[0] = 23;
	int* x = a;
	if (*x != 23) {
		//@ assert \false;
	}
	return;
}
