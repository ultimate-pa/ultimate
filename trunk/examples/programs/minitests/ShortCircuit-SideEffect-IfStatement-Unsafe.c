//#Unsafe
// Author: heizmann@informatik.uni-freiburg.de
// Date: 4.2.2013
// apparently useless while loop is used to check that no auxilliary temporary
// variable occurs in a derived loop invariant


int main() {
    int x = 1;
    int y = 1;
    _Bool z;
    if( (x++ != 0) || (y++ == 0) ) {
        z = 1;
        int a; while (a) { int b; a = b; }
    } else {
        z = 0;
        int a; while (a) { int b; a = b; }
    }
    //@ assert y == 2;
}
