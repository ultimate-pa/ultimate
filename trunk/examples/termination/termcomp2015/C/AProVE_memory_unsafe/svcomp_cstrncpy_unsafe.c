extern int __VERIFIER_nondet_int(void);

char *(cstrncpy)(char *s1, const char *s2, int n)
 {
     char *dst = s1;
     const char *src = s2;
     char *us;
     int n2;
     /* Copy bytes, one at a time.  */
     while (n > 0) {
         n--;
         if ((*dst++ = *src++) == '\0') {
             /* If we get here, we found a null character at the end
                of s2, so use memset to put null bytes at the end of
                s1.  */
             us = dst;
             n2 = n;
             while (n2-- != 0)
                 *us++ = '\0';
             break;
         }
     }
     return s1;
 }

int main() {
  char *s1;
  char *s2;
  int n = __VERIFIER_nondet_int();
  cstrncpy(s1, s2, n);
  return 0;
}
