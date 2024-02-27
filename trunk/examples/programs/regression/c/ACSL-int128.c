//#Safe
// Author: schuessf@informatik.uni-freiburg.de
// Date: 2024-02-27

int main() {
  __int128 x = -1;
  //@ assert (__int128) -1 == x;
  //@ assert (unsigned __int128) x >= 0;
}
