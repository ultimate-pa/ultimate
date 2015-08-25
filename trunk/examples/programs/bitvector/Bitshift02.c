//#Safe
/* 
 * Author: langt@informatik.uni-freiburg.de, heizmann@informatik.uni-freiburg.de
 * Date: 24.08.2015
 */

int main() {
  /* Implementation-defined behaviour of gcc */
  unsigned int a = 1U;
  unsigned long long b = 4294967296ULL;
  unsigned long long c = a << b;

  if (c != 1ULL) {
    //@ assert \false;
  }
}
