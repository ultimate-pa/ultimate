//#Safe

/*
 * Author: Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Date: 2024-01-09
 */

int main(void) {
  int *x = alloca(sizeof(int));
  int *y = alloca(sizeof(int));
  __atomic_store_n(x, 1, 5);
  __atomic_store_n(y, 0, 5);
  __atomic_load(x, y, 5);
  int val = __atomic_load_n(x, 5);
  //@ assert val == 1 && *y == 1;
}
