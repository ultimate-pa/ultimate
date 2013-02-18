//#iUnsafe
// Author: heizmann@informatik.uni-freiburg.de
// Date: 6.10.2012

int g;
int nondet;

int callee() {
    if (nondet) {
        g++;
    } else {
        g++;
    }
    return g+1;
}

int main() {
    int x = g;
    g = callee();
    //@ assert x != g-2;
}
