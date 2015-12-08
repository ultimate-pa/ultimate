//#Safe
/* 
 * Author: langt@informatik.uni-freiburg.de, heizmann@informatik.uni-freiburg.de
 * Date: 24.08.2015
 */

extern void __VERIFIER_error() __attribute__ ((__noreturn__));

int main() {
  unsigned char c = 1U;
  signed int i = ~c;

  if (i >= 0) {
    __VERIFIER_error();
  }  
}
