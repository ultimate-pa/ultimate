//#Unsafe
/* 
 * Author: langt@informatik.uni-freiburg.de
 * Date: 17.08.2015
 */

int main() {
  /* PROBLEMATIC signed int to unsigned int */
  signed int a = -1;
  unsigned int b = a;
  unsigned int limit2 = 100U;

  //assert(b > limit2);

  /* unsigned int to signed int (fitting) */
  unsigned int c = 100U;
  signed int d = c;

  //@assert(d == 100);

  /* signed int to signed long long */
  signed int e = -1;
  signed long long f = e;

  //@assert(f == -1);

  /* PROBLEMATIC signed int to unsigned long long */
  signed int g = -1;
  unsigned long long h = g;
  unsigned long long limit3 = 100ULL;

  //assert(h > limit3);

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

  /* unsigned int to signed int (not fitting) */
  if (sizeof(int) == 4) {
    unsigned int p = 2147483648U + 1U;
    signed int q = p;

    //@assert(q == 1);
  }
}
