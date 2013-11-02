/*
 * Date: November 2013
 * Author: Christian Schilling
 * 
 * An incomplete struct definition messes up the complete definition.
 */
struct A; /* this line is what causes the error */

struct A {
   int i;
};

int main() {
    struct A *p;
    return 0;
}
