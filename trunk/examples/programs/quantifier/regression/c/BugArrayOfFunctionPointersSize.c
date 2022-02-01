//#Safe
/* Bug: sizeOf the array is -4938268.
 * Minimized version of ldv-memsafety/memleaks_test23_1_true-valid-memsafety.i
 * 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2016-12-30
 * 
 */


int foo() {
    return 0;
}


int main(void) {
	int (*arrayOfFunctionPointers[])() = { foo };
//    arrayOfFunctionPointers[0];
    *arrayOfFunctionPointers;
    return 0;
}
