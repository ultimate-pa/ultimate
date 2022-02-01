/*
 * Date: November 2013
 * Author: Christian Schilling
 * 
 * The function result pointer becomes
 * the offset of a new pointer.
 */
int* func() {
    int* p;
    return p;
}

int main() {
    int *p;
    p = func();

    return (0);
}
 
