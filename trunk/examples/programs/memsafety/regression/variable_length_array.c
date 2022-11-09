//#Unsafe
/*
  Author: Frank Schüssele (schuessf@informatik.uni-freiburg.de)
  Date: 2022-10-17
*/

typedef long unsigned int size_t;

extern unsigned int __VERIFIER_nondet_uint(void);

extern void abort(void);
void assume_abort_if_not(int cond) {
  if(!cond) {abort();}
}

int main() {
  unsigned int size = __VERIFIER_nondet_uint();
  assume_abort_if_not(size != 0);
  int a[size];
  a[0] = 5;
  int x = a[0];
}