//#Safe
/*
  Author: Frank Schüssele (schuessf@informatik.uni-freiburg.de)
  Date: 2022-11-16
*/

typedef long unsigned int size_t;

extern unsigned int __VERIFIER_nondet_uint(void);

extern void abort(void);
void assume_abort_if_not(int cond) {
  if(!cond) {abort();}
}

int main() {
  int a[-1];
  a[0] = 5;
  int x = a[0];
}