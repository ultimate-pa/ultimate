/*
 * Date: October 2013
 * Author: Christian Schilling
 * 
 * Struct initialization is not supported.
 */
typedef struct Outer {
    int a;
    struct Inner {
        int c;
    } *b;
} Stuff;

int main() {
    struct Inner i = {3};
    struct Outer o = {2, & i};
    
    return 0;
}
