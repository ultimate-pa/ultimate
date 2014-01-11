//#Safe
// Author: heizmann@informatik.uni-freiburg.de
// Date: 27.2.2013


int main(int n) {
    int a;
    a = (n > 0) ? 23 : 42;
    //@ assert n == -1 ==> a == 42;
    //@ assert n == 1 ==> a == 23;   
}