//#Safe

/*
  Author: Frank Schüssele (schuessf@informatik.uni-freiburg.de)
  Date: 2022-12-15
*/

int main() {
  int* x = malloc(sizeof(int));
  long long res = *x + 1LL;
  //@ assert res <= 4294967296;
}