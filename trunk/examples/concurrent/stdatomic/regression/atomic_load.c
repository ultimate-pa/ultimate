//#Safe

/*
 * Author: Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Date: 2023-08-07
 */

int main(void) {
  int x = 0;
  int y = 1;
  __atomic_load(&x, &y, 5);
  //@ assert x == 0 && y == 0;
}
