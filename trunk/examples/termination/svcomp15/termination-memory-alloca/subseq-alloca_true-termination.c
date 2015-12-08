#include <stdlib.h>

extern int __VERIFIER_nondet_int(void);

int (subseq)(char *s, char *t)
 {
     char *ps = s;
     char *pt = t;
     while (*ps != '\0' && *pt != '\0') {
       if (*ps == *pt) {
         ps++;
       }
       pt++;
     }
     if (*pt == '\0') return 1;
     else return 0;
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
  return subseq(nondetString1,nondetString2);
}
