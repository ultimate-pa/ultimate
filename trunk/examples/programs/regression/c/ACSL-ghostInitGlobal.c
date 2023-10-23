//#Safe
// Author: schuessf@informatik.uni-freiburg.de
// Date: 2023-09-18

//@ ghost int i = 0;

int main() {
  int x = 0;
  //@ assert x == i;
  return 0;
}
