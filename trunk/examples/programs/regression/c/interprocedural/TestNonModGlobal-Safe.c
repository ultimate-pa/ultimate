//#Safe
// Author: heizmann@informatik.uni-freiburg.de
// Date: 6.10.2012

int g;

int callee() {
    int nondet;
    int res;
    if (nondet) {
        res = g;
    } else {
        res = g;
    }
    return res;
}

int main() {
    int a = callee();
    //@ assert a == g;
}

int delay() {
    int delayVar;
    delayVar++;
}