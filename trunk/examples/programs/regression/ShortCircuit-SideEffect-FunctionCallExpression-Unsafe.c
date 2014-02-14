//#Unsafe
// Author: heizmann@informatik.uni-freiburg.de
// Date: 4.2.2013

_Bool identity(_Bool b) {
    return b;
}

int main() {
    int x = 1;
    int y = 1;
    _Bool z = identity((x++ != 0) || (y++ == 0));
    //@ assert y == 2;
}
