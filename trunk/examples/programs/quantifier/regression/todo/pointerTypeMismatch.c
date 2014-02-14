/*
 * Date: October 2013
 * Author: Christian Schilling
 * 
 * 1. Cast pointer to int.
 * 2. i1 is declared as a pointer.
 */
int main(void) {
    int i1;
    int i2;
    int *p1;
    p1 = & i1;
    i2 = (int)p1;
    
    return 0;
}
