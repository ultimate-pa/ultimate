//#Safe
/* 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2017-11-18
 * 
 */
#include <stdlib.h>
#include <stdio.h>

typedef struct myStruct {
   int firstValue : 2;
   int adressAbleValue;
} EfficientStorage;

int nonMain(void) {
	EfficientStorage offHeap;
	int yOff = -3;
	offHeap.firstValue = yOff;
	int xOff = offHeap.firstValue;
	printf("%d\n",xOff);
	if (xOff != 1) {
		//@ assert \false;
	}
	
	
	int yOn = -3;
	EfficientStorage *onHeap = malloc(sizeof(EfficientStorage));
	onHeap->firstValue = yOn;
	int xOn = onHeap->firstValue;
	printf("%d\n",xOn);
	if (xOn != 1) {
		//@ assert \false;
	}

	
	return 0;
}
