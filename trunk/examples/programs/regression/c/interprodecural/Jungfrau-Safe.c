//#Safe
// Author: heizmann@informatik.uni-freiburg.de
// Date: 6.10.2012

int g;

int callee(int b) {
    int nondet;
    g = b;
    if (nondet) {
        g++;
    } else {
        g++;
    }
    return g+1;
}

int main() {
    int x = g;
    g = callee(g+1);
    //@ assert x == g-3;
}
