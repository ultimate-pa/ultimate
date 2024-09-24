//#Safe

/*
 * Author: Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Date: 2023-12-04
 */

int main(void) {
  int x = 1;
  int y = __atomic_load_n(&x, 5);
  //@ assert x == 1 && y == 1;
}
