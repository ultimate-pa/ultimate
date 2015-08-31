//#Safe
/* 
 * Author: langt@informatik.uni-freiburg.de
 * Date: 18.08.2015
 */

int main() {
  /* signed int to unsigned int */
  signed int a = -1;
  unsigned int b = a;
  unsigned int limit2 = 100U;

  if (b <= limit2) {
    //@ assert \false;
  }

  /* unsigned int to signed int (fitting) */
  unsigned int c = 100U;
  signed int d = c;

  //@assert(d == 100);

  /* signed int to signed long long */
  signed int e = -1;
  signed long long f = e;

  if (f != -1LL) {
    //@assert(\false);
  }

  /* signed int to unsigned long long */
  signed int g = -1;
  unsigned long long h = g;
  unsigned long long limit3 = 100ULL;

  if (h <= limit3) {
    //@ assert \false;
  }

  /* unsigned int to signed long long */
  unsigned int k = 100U;
  signed long long l = k;

  if (l != 100LL) {
    //@assert(\false);
  }

  /* unsigned int to unsigned long long */
  unsigned int m = 100U;
  unsigned long long n = m;

  if (n != 100ULL) {
    //@assert(\false);
  }
}
