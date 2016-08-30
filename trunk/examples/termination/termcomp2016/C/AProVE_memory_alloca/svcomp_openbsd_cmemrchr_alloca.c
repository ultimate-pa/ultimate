#include <stdlib.h>

extern int __VERIFIER_nondet_int(void);

/*
 * Reverse memchr()
 * Find the last occurrence of 'c' in the buffer 's' of size 'n'.
 */
void *
cmemrchr(const void *s, int c, size_t n)
{
	const unsigned char *cp;

	if (n != 0) {
		cp = (unsigned char *)s + n;
		do {
			if (*(--cp) == (unsigned char)c)
				return((void *)cp);
		} while (--n != 0);
	}
	return(NULL);
}

int main() {
  int length = __VERIFIER_nondet_int();
  int n = __VERIFIER_nondet_int();
  int c = __VERIFIER_nondet_int();
  if (length < 1) {
      length = 1;
  }
  if (n < 1) {
      n = 1;
  }
  char* nondetArea = (char*) alloca(n * sizeof(char));
  cmemrchr(nondetArea, c, n);
  return 0;
}
