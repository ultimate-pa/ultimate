//#Safe
// Author: schuessf@informatik.uni-freiburg.de
// Date: 2023-09-18

int main() {
  int x = 0;
  //@ ghost int i = 0;
  //@ assert x == i;
  return 0;
}
