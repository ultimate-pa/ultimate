//#iUnsafe
// Author: heizmann@informatik.uni-freiburg.de
// Date: 6.10.2012

int g;
int nondet;

int callee(int b) {
    int res;
    if (nondet) {
        res = b+1;
    } else {
        delay();
        res = b;
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