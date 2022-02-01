//#Unsafe
// Author: heizmann@informatik.uni-freiburg.de
// Date: 4.2.2013

int main() {
    int x = 1;
    int y = 1;
    (x++ != 0) || (y++ == 0);
    //@ assert y == 2;
}
