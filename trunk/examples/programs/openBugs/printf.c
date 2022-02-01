//#Unsafe
// Author: heizmann@informatik.uni-freiburg.de
// Date: 22.10.2012
// Test if our bogus translation of printf (return some int) works.


extern int __VERIFIER_nondet_int();

int main(void) {
  char *s;
  s = "Waldkirch";
  printf("%s", s);
  int i = printf("%s", s);
  if (i == 0) {
       ERROR:
       goto ERROR;
  }
}
