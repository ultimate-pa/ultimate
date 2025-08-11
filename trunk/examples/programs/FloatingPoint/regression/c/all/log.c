// #Safe
/*
 * Date: 2025-08-11
 * Author: schuessf@informatik.uni-freiburg.de
 */

int main() {
  float x = __VERIFIER_nondet_float();
  float y = logf(x);
  if (isnan(x) && !isnan(y)) reach_error();
  if (x == 0 && !isinf(y)) reach_error();
  if (x == 1 && y != 0) reach_error();
  if (x > 1 && y <= 0) reach_error();
  if (x >= 0 && y > x-1) reach_error();
}
