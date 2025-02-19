//#Safe
/*
 * Date: 2024-12-10
 * Author: schuessf@informatik.uni-freiburg.de
 *
 * Test for the bitwise operations (| and &) on boolean operands
 * To simplify our translation (esp. in integer mode), we handle
 * this similarly to && and ||, except for short-circuiting.
 */

int main() {
  int x = __VERIFIER_nondet_int();
  int y = __VERIFIER_nondet_int();
  if (x == 0 & y == 0) return;
  if (x != 0 | y != 0) return;
  reach_error();
}
