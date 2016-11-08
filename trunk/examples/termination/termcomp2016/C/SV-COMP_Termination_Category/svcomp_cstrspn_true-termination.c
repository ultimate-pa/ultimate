/*
 * Date: 17.12.2013
 * Author: Thomas Ströder
 */
#include <stdlib.h>

extern int __VERIFIER_nondet_int(void);

/* Returns some null-terminated string. */
char* __VERIFIER_nondet_String(void) {
    int length = __VERIFIER_nondet_int();
    if (length < 1) {
        length = 1;
    }
    char* nondetString = (char*) malloc(length * sizeof(char));
    nondetString[length-1] = '\0';
    return nondetString;
}





int (cstrspn)(const char *s1, const char *s2)
 {
     const char *sc1;
     const char *s;
     int c;
     for (sc1 = s1; *sc1 != '\0'; sc1++) {
         s = s2;
         c = *sc1;
         while (*s != '\0' && *s != (char)c)
             s++;
         if (*s != c)
             return (sc1 - s1);
     }
     return sc1 - s1;            /* terminating nulls don't match */
 }

int main() {
    return cstrspn(__VERIFIER_nondet_String(),__VERIFIER_nondet_String());
}


