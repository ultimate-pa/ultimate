/*
 * Date: October 2013
 * Author: Christian Schilling
 * 
 * AssertionError in ArrayHandler:
 * assert rexId.cType instanceof CArray;
 * -> rexId.cType instanceof CPointer
 */
int main() {
    int *a;
    if (a[2] != 3)
        return 1;
    return 0;
}
