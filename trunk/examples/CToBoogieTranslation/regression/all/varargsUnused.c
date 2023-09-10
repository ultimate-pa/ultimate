//#Safe
/*
  Author: Frank Schüssele (schuessf@informatik.uni-freiburg.de)
  Date: 2022-12-05
*/

int vargArgFunction(int count, ...) {
   return 0;
}

int main() {
  int x = vargArgFunction(2, 1,2);
  int y = vargArgFunction(0);
  //@ assert x == y;
}