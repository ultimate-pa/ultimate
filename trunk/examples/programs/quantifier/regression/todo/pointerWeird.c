/*
 * Date: November 2013
 * Author: Christian Schilling
 * 
 * Weird pointer casts are not supported.
 */
int main() {
    int i;
    int* vp;
    *((int **)i) = vp;
}
