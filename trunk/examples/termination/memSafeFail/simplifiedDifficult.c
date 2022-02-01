#include <stdlib.h>

extern int __VERIFIER_nondet_int(void);

void cstrcpy(char *s1, char *s2)
 {
     /* Do the copying in a loop.  */
     while ((*s1++ = *s2++) != '\0')
         ;               /* The body of this loop is left empty. */
     /* Return the destination string.  */
 }

int main() {
  int length2 = __VERIFIER_nondet_int();
  if (length2 < 1) {
      length2 = 1;
  }
  char* nondetString = (char*) alloca(length2 * sizeof(char));
  nondetString[length2-1] = '\0';
  cstrcpy(nondetString,nondetString);
  return 0;
}
  
