//#Safe
// Author: schuessf@informatik.uni-freiburg.de
// Date: 2024-02-08

int* z;

//@ ensures y == 0;
int f() {
  //@ assert x == y;
}

int x, y;

int main() {
  z = &x;
  f();
}
