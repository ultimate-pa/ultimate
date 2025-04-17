// #Safe
/*
 * Date: 2025-01-07
 * Author: schuessf@informatik.uni-freiburg.de
 *
 */

int* a;

//@ ensures a[0] == 7;
void init() {
  a[0] = 7;
}

int main() {
  a = malloc(sizeof(int));
  if (a == NULL) return;
  init();
  //@ assert *a == 7;
}
