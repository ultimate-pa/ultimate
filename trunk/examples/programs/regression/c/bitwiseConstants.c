//#Safe
/*
  Author: Frank Schüssele (schuessf@informatik.uni-freiburg.de)
  Date: 2022-11-29
*/

int main() {
	int r;

  r = 2 & 3;
  //@ assert r == 2;
}
