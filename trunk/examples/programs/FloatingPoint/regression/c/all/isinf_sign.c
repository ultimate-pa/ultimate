// #Safe
/*
 * Date: 2025-08-11
 * Author: schuessf@informatik.uni-freiburg.de
 */

int main() {
  int x = __builtin_isinf_sign(5.7);
  int y = __builtin_isinf_sign(INFINITY);
  int z = __builtin_isinf_sign(-INFINITY);
  //@ assert x == 0;
  //@ assert y > 0;
  //@ assert z < 0;
}
