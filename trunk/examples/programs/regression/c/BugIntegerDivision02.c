//#Safe
// Author: heizmann@informatik.uni-freiburg.de
// Date: 27.12.2014
// Bug: Division of 0 (not by 0) does not work.

int main() {
    int res1 = 0 / 23;
    //@ assert res1 == 0;
    int res2 = 0 % 23;
    //@ assert res2 == 0;
    return 0;
}