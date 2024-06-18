//#Safe
// Author: schuessf@informatik.uni-freiburg.de
// Date: 2024-06-18
//
// The result of __VERIFIER_nondet_bool has to be between 0 and 1

int main(void) {
	if (__VERIFIER_nondet_bool() > 1 || __VERIFIER_nondet_bool() < 0) {
    reach_error();
  }
}
