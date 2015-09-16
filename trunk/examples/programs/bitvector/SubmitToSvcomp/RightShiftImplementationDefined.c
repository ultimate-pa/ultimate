//#Safe
/* 
 * Author: langt@informatik.uni-freiburg.de, heizmann@informatik.uni-freiburg.de
 * Date: 24.08.2015
 */

extern void __VERIFIER_error() __attribute__ ((__noreturn__));

int main() {
  int a = -1;
  int b = a >> 1;

  if (b != -1) {
    __VERIFIER_error();
  }
}
