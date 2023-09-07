//#Safe
// Author: schuessf@informatik.uni-freiburg.de
// Date: 2023-09-04

int main() {
  int r = ({ int x = 0; x+1; });
  //@ assert r == 1;
  return 0;
}
