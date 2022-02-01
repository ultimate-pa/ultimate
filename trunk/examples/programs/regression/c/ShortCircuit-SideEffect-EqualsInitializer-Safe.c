//#Safe
// Author: heizmann@informatik.uni-freiburg.de
// Date: 4.2.2013

int main() {
    int x = 1;
    int y = 1;
    _Bool z = (x++ == 0) || (y++ == 0);
    //@ assert x == 2 && y == 2;
}
