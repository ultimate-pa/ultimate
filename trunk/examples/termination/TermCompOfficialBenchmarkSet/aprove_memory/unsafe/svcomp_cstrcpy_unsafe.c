char *(cstrcpy)(char *s1, const char *s2)
 {
     char *dst = s1;
     const char *src = s2;
     /* Do the copying in a loop.  */
     while ((*dst++ = *src++) != '\0')
         ;               /* The body of this loop is left empty. */
     /* Return the destination string.  */
     return s1;
 }

int main() {
  char* s2;
  char* s1;
  cstrcpy(s1, s2);
  return 0;
}
  
