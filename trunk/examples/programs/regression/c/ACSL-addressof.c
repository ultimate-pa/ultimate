// #Safe
/*
 * Date: 2024-01-29
 * Author: schuessf@informatik.uni-freiburg.de
 *
 */

int main() {
  int x;
  int *p = &x;
  //@ assert p == &x;
}
