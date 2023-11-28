//#Safe
/* Check some basic properties of realloc. It would be better to add
 * a few more checks.
 * 
 * Date: 2023-11-26
 * Author: heizmann@informatik.uni-freiburg.de
 * 
 */

#include <stdlib.h>
#include <string.h>
#include <stdio.h>

int main() {
	char *oldSegment = malloc(2*sizeof(char));
	*oldSegment = 17;
	*(oldSegment+1) = 42;
	char *newSegment = realloc(oldSegment, 3*sizeof(char));
	char fst = *newSegment;
	printf("%d\n",fst);
	//@ assert fst == 17;
	char snd = *(newSegment+1);
	printf("%d\n",snd);
	//@ assert snd == 42;
	free(newSegment);
	
	return 0;
}


void otherFun() {
	// some useless code to make sure that we also have a pointer array
	void **ptr = malloc(sizeof(void *));
	*ptr = ptr;
	
	
	
	// some useless code to make sure that other data types are also stored on the heap
	unsigned char *ptrUchar = malloc(sizeof(unsigned char));
	*ptrUchar = 42;
	
	short *ptrShort = malloc(sizeof(short));
	*ptrShort = 42;
	unsigned short *ptrUshort = malloc(sizeof(unsigned short));
	*ptrUshort = 42;
	
	int *ptrInt = malloc(sizeof(int));
	*ptrInt = 42;
	unsigned int *ptrUint = malloc(sizeof(unsigned int));
	*ptrUint = 42;
	
	long *ptrLong = malloc(sizeof(long));
	*ptrLong = 42;
	unsigned long *ptrUlong = malloc(sizeof(unsigned long));
	*ptrUlong = 42;

	
}
