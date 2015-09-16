//#Safe
/* 
 * Author: langt@informatik.uni-freiburg.de, heizmann@informatik.uni-freiburg.de
 * Date: 24.08.2015
 */

extern void __VERIFIER_error() __attribute__ ((__noreturn__));

int main() {
  char c = 1;

  if (sizeof(char) < sizeof(int)) {
    if (sizeof(+c) != sizeof(int)) {
      __VERIFIER_error();
    }

    if (sizeof(-c) != sizeof(int)) {
      __VERIFIER_error();
    }

    if (sizeof(~c) != sizeof(int)) {
      __VERIFIER_error();
    }
  }
}
