// #Unsafe
/*
 * Date: 2015-08-23
 * Author:  heizmann@informatik.uni-freiburg.de
 */

#include <stdlib.h>
#include <stdio.h>

int main();

int main() {
	int *p = malloc(sizeof(int));
	char *q = (char *) p;
	*p = 12345678;
	printf("%d\n",*p);
	q++;
	*q = 5;
	int x = *p;
	//@ assert x == 12345678;
	printf("%d\n",*p);
	printf("%d\n",*q);

}