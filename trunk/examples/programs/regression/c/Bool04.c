//#Safe
// Author: schuessf@informatik.uni-freiburg.de
// Date: 2024-06-18
//
// The result of __VERIFIER_nondet_bool has to be between 0 and 1

int main(void) {
  _Bool x = __VERIFIER_nondet_bool();
  _Bool y = __VERIFIER_nondet_bool();
  if (x + y > 2 || x + y < 0) reach_error();
}
