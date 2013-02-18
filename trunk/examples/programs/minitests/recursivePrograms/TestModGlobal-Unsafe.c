//#iUnsafe
// Author: heizmann@informatik.uni-freiburg.de
// Date: 6.10.2012

int g;
int nondet;

int callee() {
    if (nondet) {
        g++;
    } else {
        delay();
    }
    return;
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