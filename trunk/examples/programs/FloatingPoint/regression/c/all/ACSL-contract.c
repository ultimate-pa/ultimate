//#Safe
/* 
 * Test for ACSL contracts using float.
 * 
 * Author: schuessf@informatik.uni-freiburg.de
 * Date: 2024-02-23
 * 
 */

//@ ensures \result > -0.1 && \result < 0.1;
float zero() {
  return 0.0;
}

int main() {
  float z = zero();
  //@ assert z > -0.1 && z < 0.1;
}
