//#iUnsafe
// Author: heizmann@informatik.uni-freiburg.de
// Date: 6.10.2012

int g;

int callee() {
    int nondet;
    if (nondet) {
        g++;
    } else {
        delay();
    }
    return 0;
}

int main() {
    int a = g;
    callee();
    //@ assert a == g-1;
}

int delay() {
    int delayVar;
    delayVar++;
}