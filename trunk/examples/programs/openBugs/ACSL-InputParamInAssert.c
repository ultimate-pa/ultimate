//#Safe
// Author: heizmann@informatik.uni-freiburg.de
// Date: 27.2.2013


int main(int n) {
    n++;
    //@ assert \old(n) == n;
}