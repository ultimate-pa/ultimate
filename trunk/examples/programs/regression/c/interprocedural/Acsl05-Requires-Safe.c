//#Safe
// Author: heizmann@informatik.uni-freiburg.de
// Date: 2023-07-11

extern int __VERIFIER_nondet_int();

int g;

/*@ requires (g > i);
  @*/
void callee(int i) {
    return;
}

int main() {
    g = 42;
    int x = 23;
    callee(23);
}
