//#Safe
/*
 * Luxembourg.bpl translated to a C program (without overflows).
 * The loop invariant 1000-y>=x allows us to prove correctness.
 * 
 * Date: 2024-08-02
 * Author: schuessf@informatik.uni-freiburg.de
 *
 */

int main() {
  int x = 0;
  int y = 1000;

  while (__VERIFIER_nondet_int() && x < 2147483647) {
    x++;
    y--;
  }

  if (x == 1000 && y > 0) {
    reach_error();
  }
}
