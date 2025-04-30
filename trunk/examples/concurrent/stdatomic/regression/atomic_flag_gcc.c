//#Safe

/*
 * Author: Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Date: 2023-08-07
 */

int main(void) {
  _Bool x = 0;
  _Bool y = __atomic_test_and_set(&x, 5);
  //@ assert x == 1 && y == 0;
  __atomic_clear(&x, 5);
  //@ assert x == 0;
}
