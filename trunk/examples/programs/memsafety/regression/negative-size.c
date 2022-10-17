//# Safe
/*
  Author: Frank Schüssele (schuessf@informatik.uni-freiburg.de)
  Date: 2022-10-17  
*/

typedef long unsigned int size_t;

void * __attribute__((__cdecl__)) malloc (size_t __size) ;

extern int __VERIFIER_nondet_int(void);

extern void abort(void);
void assume_abort_if_not(int cond) {
  if(!cond) {abort();}
}

int main() {
  int size = __VERIFIER_nondet_int();
  assume_abort_if_not(size != 0);
	int *a = malloc(sizeof(int) * size);
	int x = a[0];
}