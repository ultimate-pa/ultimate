//#Safe
/* 
 * Author: langt@informatik.uni-freiburg.de, heizmann@informatik.uni-freiburg.de
 * Date: 24.08.2015
 */

extern void __VERIFIER_error() __attribute__ ((__noreturn__));

int main() {
  if (sizeof(int) == 4) {
    unsigned int a = 2147483648;  // 2^31
    unsigned int b = a >> 1;

    if (b != 1073741824U) {       // 2^30
      __VERIFIER_error();
    }
  }
}
