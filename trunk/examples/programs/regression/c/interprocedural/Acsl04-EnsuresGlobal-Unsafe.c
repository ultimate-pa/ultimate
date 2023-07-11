//#Unsafe
// Author: heizmann@informatik.uni-freiburg.de
// Date: 2023-07-11

extern int __VERIFIER_nondet_int();

int g;

/*@ ensures (g > \old(g));
  @*/
void callee() {
    while(__VERIFIER_nondet_int()) {
        g++;
    }
    return;
}

int main() {
    g = __VERIFIER_nondet_int();
    callee();
}
