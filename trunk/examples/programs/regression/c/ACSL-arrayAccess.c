// #Safe
/*
 * Date: 2024-01-29
 * Author: schuessf@informatik.uni-freiburg.de
 *
 */

int main() {
  int *p = malloc(sizeof(int));
  *p = 42;
  int a[2] = {1, 2};
  //@ assert p[0] == 42 && a[1] == 2;
}