//#Safe
// Author: schuessf@informatik.uni-freiburg.de
// Date: 2024-01-24

int main() {
  int *p = 0;
  //@ assert (unsigned long long) p == 0;
  //@ assert p == (int*) 0;
}