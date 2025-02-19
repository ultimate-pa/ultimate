//#Safe

/*
 * Author: Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Date: 2024-01-09
 */

int main(void) {
  int x = 0;
  int y = 1;
  y = __atomic_exchange_n(&x, y, 5);
  //@ assert x == 1 && y == 0;
  __atomic_load(&x, &y, 5);
  int* px = &x;
  int* py = &y;
  //@ assert *px == 1 && *py == 1;
}
