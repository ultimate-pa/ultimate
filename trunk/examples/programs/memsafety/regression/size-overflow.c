//#Safe
/*
  Author: Frank Schüssele (schuessf@informatik.uni-freiburg.de)
  Date: 2022-10-19
*/

typedef long unsigned int size_t;

void * __attribute__((__cdecl__)) malloc (size_t __size) ;
extern void free (void *__ptr) __attribute__ ((__nothrow__ , __leaf__));

extern unsigned int __VERIFIER_nondet_uint(void);

extern void abort(void);
void assume_abort_if_not(int cond) {
  if(!cond) {abort();}
}

int main() {
  unsigned int size = __VERIFIER_nondet_uint();
  assume_abort_if_not(size > 0 && size < 4294967296 / sizeof(int));
  int *a = malloc(sizeof(int) * size);
  a[0] = 5;
  int x = a[0];
  free(a);
}