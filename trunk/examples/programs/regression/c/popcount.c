//#Safe
/*
  Author: Frank Schüssele (schuessf@informatik.uni-freiburg.de)
  Date: 2023-11-10
*/

int main() {
  int ones = __builtin_popcount(0);
  //@ assert ones == 0;
}