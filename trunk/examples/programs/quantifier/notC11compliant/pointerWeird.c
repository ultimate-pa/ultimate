/*
 * Date: November 2013
 * Author: Christian Schilling
 * 
 * Weird pointer casts are not supported.
 */
int main() {
    long i;
    int* vp;
    *((long **)i) = vp;
}
