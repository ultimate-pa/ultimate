//#termcomp16-someonesaidyes
//#termcomp16-someonesaidyes
typedef enum {false, true} bool;

extern int __VERIFIER_nondet_int(void);

int main() {
  int i, sum, bound;
  bound = __VERIFIER_nondet_int();
  i = 0;
  sum = 0;
  while (i<bound) {
    sum = sum + i;
    i = i + 1;
  }
  return 0;
}
