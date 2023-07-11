//#Unsafe
// Author: heizmann@informatik.uni-freiburg.de
// Date: 2023-07-11

extern int __VERIFIER_nondet_int();

int g;

/*@ ensures (\result > i);
  @*/
int callee(int i) {
    while(__VERIFIER_nondet_int()) {
        i++;
    }
    return i;
}

int main() {
    int x = __VERIFIER_nondet_int();
    g = callee(x);
}
