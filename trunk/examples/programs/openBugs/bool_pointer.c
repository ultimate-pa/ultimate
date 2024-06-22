//#Safe
// Author: schuessf@informatik.uni-freiburg.de
// Date: 2024-06-18
//
// ULTIMATE claims this program to be incorrect, whereas when compiled with GCC, we do not call reach_error.
// We are not sure about the expected result, it depends whether there is an implicit conversion for *y to _Bool.

int main() {
  char x = 'a';
  _Bool* y = (_Bool*)&x;
  if (*y > 2) reach_error();
}
