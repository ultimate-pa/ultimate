//#Safe
// Author: schuessf@informatik.uni-freiburg.de
// Date: 2023-09-18

int main() {
  //@ ghost int i;
  int x = 0;
  //@ ghost i = x;
  //@ assert x == i;
  return 0;
}
