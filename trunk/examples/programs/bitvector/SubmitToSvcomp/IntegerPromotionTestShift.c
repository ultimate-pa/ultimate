//#Safe
/* 
 * Author: langt@informatik.uni-freiburg.de, heizmann@informatik.uni-freiburg.de
 * Date: 24.08.2015
 */

extern void __VERIFIER_error() __attribute__ ((__noreturn__));

int main() {
  unsigned char a = 128U;
  unsigned char b = 1U;
  int i = a << b;

  if (i != 256) {
    __VERIFIER_error();
  }
}
