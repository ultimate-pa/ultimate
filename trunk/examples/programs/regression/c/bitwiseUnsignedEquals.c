//#Safe
/*
  Author: Frank Schüssele (schuessf@informatik.uni-freiburg.de)
  Date: 2022-11-29
*/

int main() {
	unsigned int r, x, y;

  if (x != y) return;
  r = x | y;
  //@ assert r == x;
}
