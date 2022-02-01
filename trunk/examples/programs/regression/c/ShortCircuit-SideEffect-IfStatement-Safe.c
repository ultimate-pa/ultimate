//#Safe
// Author: heizmann@informatik.uni-freiburg.de
// Date: 4.2.2013

int main() {
    int x = 1;
    int y = 1;
    _Bool z;
    if( (x++ == 0) || (y++ == 0) ) {
        z = 1;
        int a; while (a) { int b; a = b; }
    } else {
        z = 0;
        int a; while (a) { int b; a = b; }
    }
    //@ assert x == 2 && y == 2 && z == 0;
}
