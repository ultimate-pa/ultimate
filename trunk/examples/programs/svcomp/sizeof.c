//#Unsafe
// Author: heizmann@informatik.uni-freiburg.de
// Date: 22.10.2012
// Test if our bogus translation of sizeof (return arbitrary int) works.



int main(void) {
  int i;
  i = sizeof(long);
  if (i == 4) {
       ERROR:
       goto ERROR;
  }
}
