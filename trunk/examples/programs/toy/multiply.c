//#Safe

/*
 * Simple multiplication function using addition iteratively,
 * annotated with procedure contract and loop invariant.
 *
 * Author: Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Date: 2023-07-11
 *
 */

/*@ requires y >= 0;
  @ ensures \result == x * y;
  @*/
int multiply(int x, int y) {
    int r = 0;
    //@ loop invariant r == x * i && i <= y;
    for (int i = 0; i < y; i++) {
      r += x;
    }
    return r;
}