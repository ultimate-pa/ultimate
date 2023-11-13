//#Safe
// Author: heizmann@informatik.uni-freiburg.de
// Date: 2023-11-05
//
// Reveals problems with backtranslation of invariants if we use
// procedure inlining.

extern int __VERIFIER_nondet_int();

int g;


int callee(int i) {
    while(__VERIFIER_nondet_int() && i < 1000) {
        i++;
    }
    return i;
}

int main() {
    int c = 5;
    g = callee(c);
    //@ assert c == 5 && g >=5;
}
