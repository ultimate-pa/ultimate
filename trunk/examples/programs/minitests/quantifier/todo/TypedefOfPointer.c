//#iSafe
/*
 * Date: October 2013
 * Author: heizmann@informtik.uni-freiburg.de
 * 
 */

typedef int* intPointer;

int main() {
    int *p = malloc(sizeof(int));
    intPointer q;
    q = p;
    free(q);
    return 0;
}
