//#Unsafe
// Author: heizmann@informatik.uni-freiburg.de
// Date: 6.10.2012

int g;

int delay() {
    int delayVar;
    delayVar++;
}

int callee() {
    int nondet;
    int res;
    if (nondet) {
        res = g;
    } else {
        delay();
    }
    return res;
}

int main() {
    int a = callee();
    //@ assert a == g;
}

