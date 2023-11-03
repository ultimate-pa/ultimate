//#Safe

/*
  Author: Frank Schüssele (schuessf@informatik.uni-freiburg.de)
  Date: 2022-12-19
*/

int main() {
  int x, y;
  x = y & (-4);
  //@ assert y < 4 || y > 7 || x == 4;
}