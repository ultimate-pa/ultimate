//#Safe
/*
 * Date: October 2013
 * Author: heizmann@informtik.uni-freiburg.de
 * 
 */

//int* intPointer;
typedef int* intPointer;

int main() {
    int *p = malloc(sizeof(int));
	int *q;
	q = p;
    return 0;
}
