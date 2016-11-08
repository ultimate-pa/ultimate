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





int (cstrlen)(const char *s)
 {
     const char *p = s;
     /* Loop over the data in s.  */
     while (*p != '\0')
         p = p+2;
     return (int)(p - s);
 }

int main() {
    return cstrlen(__VERIFIER_nondet_String());
}


