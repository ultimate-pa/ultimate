// #Safe
/*
 * Date: 2025-01-07
 * Author: schuessf@informatik.uni-freiburg.de
 *
 */

int main() {
  unsigned x = 7;
  //@ assert \forall int x; (long long) x + 1 > x;
  //@ assert x == 7;
}
