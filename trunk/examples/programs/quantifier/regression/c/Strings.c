//#Safe
// Author: heizmann@informatik.uni-freiburg.de
// Date: 22.10.2012
// Test if our bogus translation of Strings (to int) works.


extern int __VERIFIER_nondet_int();

int main(void) {
  char *s;
  s = "Waldkirch";
  char *t;
  t = (char *) "Buchholz"; // with cast
  if (s == t) {
       ERROR:
       goto ERROR;
  }
}
