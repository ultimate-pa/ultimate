//#Safe
// Author: schuessf@informatik.uni-freiburg.de
// Date: 2023-09-05

int main() {
  int r = ({ int x = 0; *&x; });
  //@ assert r == 0;
  return 0;
}
