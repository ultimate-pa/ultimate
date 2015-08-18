//#Safe
/* 
 * Author: langt@informatik.uni-freiburg.de
 * Date: 18.08.2015
 */

int main() {
  /* unsigned long long to signed int */
  if (sizeof(long long) > 4) {
    unsigned long long a = 4294967295ULL;
    signed int b = a;

    //@assert(b == -1);
  }

  /* signed long long to signed int */
  if (sizeof(long long) > 4) {
    signed long long c = -9223372034707292161;
    signed int d = c;

    //@assert(d == 2147483647);
  }

  /* unsigned int to signed int */
  if (sizeof(int) == 4) {
    unsigned int e = 4294967295U;
    signed int f = e;

    //@assert(f == -1);
  }
}
