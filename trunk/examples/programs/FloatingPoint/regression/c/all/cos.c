// #Safe
/*
 * Date: 2025-08-11
 * Author: schuessf@informatik.uni-freiburg.de
 */

int main() {
  float x = __VERIFIER_nondet_float();
  float y = cosf(x);
  if (isnan(x) && !isnan(y)) reach_error();
  if (isinf(x) && !isnan(y)) reach_error();
  if (x == 0 && y != 1) reach_error();
  if (y > 1 || y < -1) reach_error();
}
