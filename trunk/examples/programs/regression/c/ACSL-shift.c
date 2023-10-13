// #Safe
/*
 * Test for shift operators in ACSL expressions
 * 
 * Date: 2023-09-21
 * Author: schuessf@informatik.uni-freiburg.de
 *
 */

extern int __VERIFIER_nondet_int(void);

int main() {
  int x = 0;
  int y = __VERIFIER_nondet_int();
  //@ assert (x >> y) == 0 && (x << y) == 0;
}
