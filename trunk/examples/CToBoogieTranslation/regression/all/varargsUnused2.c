//#Unsafe
/*
  Author: Frank Schüssele (schuessf@informatik.uni-freiburg.de)
  Date: 2022-12-07
*/

int vargArgFunction(int count, ...) {
   return 0;
}

int f(int x) {
  //@ assert x == 0;
  return x;
}

int main() {
  vargArgFunction(2, f(1),2);
}