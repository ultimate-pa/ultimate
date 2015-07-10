#include <stdlib.h>

extern int __VERIFIER_nondet_int(void);

/*
 * bzero -- vax movc5 instruction
 */
void
cbzero(void *b, size_t length)
{
	char *p;

	for (p = b; length--;)
		*p++ = '\0';
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
  if (n > length) return 0;
  char* nondetArea = (char*) alloca(length * sizeof(char));
  cbzero(nondetArea, n);
  return 0;
}
