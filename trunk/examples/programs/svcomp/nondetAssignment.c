//#Unsafe
// Author: heizmann@informatik.uni-freiburg.de
// Date: 22.10.2012
// Test if __VERIFIER_nondet_int() is able to assign different values


extern int __VERIFIER_nondet_int();

int main(void) { 
  int countOldAndNewValueDifferent = 0;
  int oldValue = __VERIFIER_nondet_int();
  int newValue = __VERIFIER_nondet_int();
  while(1) {
    oldValue = newValue;
    newValue = __VERIFIER_nondet_int();
    if (oldValue != newValue) {
      countOldAndNewValueDifferent++;
    }
    if (countOldAndNewValueDifferent >= 5) {
      ERROR:
      goto ERROR;
    }
  }
}
