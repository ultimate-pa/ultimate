//#SyntaxError
// Author: heizmann@informatik.uni-freiburg.de
// Date: 4.2.2013

_Bool identity(_Bool b) {
    return b;
}

int main() {
    int x = 1;
    int y = 1;
    _Bool z = callee((x++ == 0) || (y++ == 0));
    //@ assert x == 2 && y == 2 && z == \false;
}
