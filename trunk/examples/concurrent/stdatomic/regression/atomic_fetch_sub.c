//#Safe

/*
 * Author: Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Date: 2023-08-07
 */

int main(void) {
  int x = 1;
  int y = __atomic_fetch_sub(&x, 1, 5);
  //@ assert x == 0 && y == 1;
}
