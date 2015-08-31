//#Safe
/* 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2015-08-30
 * 
 */

#include <stdlib.h>

int main() {
	int *p = malloc(4*sizeof(int));
	int *q = p;
	int *r = p + 2;
	/* aliasing pointers */
	{
		int leq = (q <= p);
		//@ assert leq == 1;
		int le = (q < p);
		//@ assert le == 0;
		int geq = (q >= p);
		//@ assert geq == 1;
		int ge = (q > p);
		//@ assert ge == 0;
	}
	
	/* non-aliasing pointers */
	{
 		int leq = (r <= p);
		//@ assert leq == 0;
		int le = (r < p);
		//@ assert le == 0;
		int geq = (r >= p);
		//@ assert geq == 1;
		int ge = (r > p);
		//@ assert ge == 1;
	}
	free(p);
	
	/* arrays */
	int a[5];
	{
		int leq = (&a[3] <= &a[0]);
		//@ assert leq == 0;
		int le = (&a[3] < &a[0]);
		//@ assert le == 0;
		int geq = (&a[3] >= &a[0]);
		//@ assert geq == 1;
		int ge = (&a[3] > &a[0]);
		//@ assert ge == 1;
	}
	return 0;
}
