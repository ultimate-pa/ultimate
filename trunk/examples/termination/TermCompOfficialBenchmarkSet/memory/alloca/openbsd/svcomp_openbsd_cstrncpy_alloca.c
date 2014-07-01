#include <stdlib.h>

extern int __VERIFIER_nondet_int(void);

/*
 * Copy src to dst, truncating or null-padding to always copy n bytes.
 * Return dst.
 */
char *
cstrncpy(char *dst, const char *src, size_t n)
{
	if (n != 0) {
		char *d = dst;
		const char *s = src;

		do {
			if ((*d++ = *s++) == 0) {
				/* NUL pad the remaining n-1 bytes */
				while (--n != 0)
					*d++ = 0;
				break;
			}
		} while (--n != 0);
	}
	return (dst);
}

int main() {
  int length = __VERIFIER_nondet_int();
  int n = __VERIFIER_nondet_int();
  if (length < 1) {
      length = 1;
  }
  if (n < 1) {
      n = 1;
  }
  char* nondetArea = (char*) alloca(n * sizeof(char));
  char* nondetString = (char*) alloca(length * sizeof(char));
  nondetString[length-1] = '\0';
  cstrncpy(nondetArea, nondetString, n);
  return 0;
}
