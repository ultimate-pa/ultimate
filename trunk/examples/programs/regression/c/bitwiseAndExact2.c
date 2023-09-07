//#Safe

/*
  Author: Frank Schüssele (schuessf@informatik.uni-freiburg.de)
  Date: 2022-12-19
*/

int main() {
  int x, y;
  x = y & 255;
  //@ assert y < 0 || y > 255 || x == y;
}