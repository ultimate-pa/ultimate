/*
 * Date: 17.12.2013
 * Author: Thomas Ströder
 */
#include <stdlib.h>

extern int __VERIFIER_nondet_int(void);

size_t
cstrlen(const char *str)
{
	const char *s;

	for (s = str; *s; ++s)
		;
	return (s - str);
}

int
cstrncmp(const char *s1, const char *s2, size_t n)
{

	if (n == 0)
		return (0);
	do {
		if (*s1 != *s2++)
			return (*(unsigned char *)s1 - *(unsigned char *)--s2);
		if (*s1++ == 0)
			break;
	} while (--n != 0);
	return (0);
}

/*
 * Find the first occurrence of find in s.
 */
char *
cstrstr(const char *s, const char *find)
{
	char c, sc;
	size_t len;

	if ((c = *find++) != 0) {
		len = cstrlen(find);
		do {
			do {
				if ((sc = *s++) == 0)
					return (NULL);
			} while (sc != c);
		} while (cstrncmp(s, find, len) != 0);
		s--;
	}
	return ((char *)s);
}

int main() {
    int length1 = __VERIFIER_nondet_int();
    int length2 = __VERIFIER_nondet_int();
    if (length1 < 1) {
        length1 = 1;
    }
    if (length2 < 1) {
        length2 = 1;
    }
    char* nondetString1 = (char*) alloca(length1 * sizeof(char));
    char* nondetString2 = (char*) alloca(length2 * sizeof(char));
    nondetString1[length1-1] = '\0';
    nondetString2[length2-1] = '\0';
    return cstrstr(nondetString1,nondetString2);
}


