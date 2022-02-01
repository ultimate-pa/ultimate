#include <stdlib.h>

extern int __VERIFIER_nondet_int(void);

/*
 * Concatenate src on the end of dst.  At most strlen(dst)+n+1 bytes
 * are written at dst (at most n+1 bytes being appended).  Return dst.
 */
char *
cstrncat(char *dst, const char *src, size_t n)
{
	if (n != 0) {
		char *d = dst;
		const char *s = src;

		while (*d != 0)
			d++;
		do {
			if ((*d = *s++) == 0)
				break;
			d++;
		} while (--n != 0);
		*d = 0;
	}
	return (dst);
}

int main() {
    int length1 = __VERIFIER_nondet_int();
    int length2 = __VERIFIER_nondet_int();
    int n = __VERIFIER_nondet_int();
    if (length1 < 1) {
        length1 = 1;
    }
    if (length2 < 1) {
        length2 = 1;
    }
    if (n < 1) {
        n = 1;
    }
    if (length1 < n || length1 - n < length2) return 0;
    char* nondetString1 = (char*) alloca(length1 * sizeof(char));
    char* nondetString2 = (char*) alloca(length2 * sizeof(char));
    nondetString1[length1-n-1] = '\0';
    nondetString2[length2-1] = '\0';
    cstrncat(nondetString1, nondetString2, n);
    return 0;
}
