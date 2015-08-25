//#Safe
/* 
 * Author: langt@informatik.uni-freiburg.de, heizmann@informatik.uni-freiburg.de
 * Date: 24.08.2015
 */

int main() {
  /* In revision 15066 the usual arithmetic conversions were applied to both
     operands, which is not allowed according to the C standard. */
  unsigned int a = 2147483648U;
  unsigned long long b = 1ULL;
  unsigned long long c = a << b;

  if (c != 0ULL) {
    //@ assert \false;
  }
}
