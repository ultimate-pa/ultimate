//#Safe
// Author: heizmann@informatik.uni-freiburg.de
// Date: 6.10.2012

int g;

int callee(int b) {
    int nondet;
    int res;
    if (nondet) {
        res = b+1;
    } else {
        res = b+1;
    }
    return res;
}

int main() {
    int x;
    int a = callee(x);
    //@ assert a == x+1;
}

int delay() {
    int delayVar;
    delayVar++;
}