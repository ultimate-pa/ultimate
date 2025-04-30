//#Safe

/*
 * Author: Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Date: 2023-08-07
 */

int main(void) {
  int x = 0;
  int y = __atomic_fetch_add(&x, 1, 5);
  //@ assert x == 1 && y == 0;
}
