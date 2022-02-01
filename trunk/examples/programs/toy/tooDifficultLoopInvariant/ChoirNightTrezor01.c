//#Safe
/*
 * Program obtained from Jochen,
 * related to some Trezor code.
 * 
 * 
 * Date: 2019-06-29
 * Author: Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * 
 */
extern int __VERIFIER_nondet_int(void);
extern void __VERIFIER_error() __attribute__ ((__noreturn__));

int main() {
  unsigned int a;
  unsigned int b;

  // avoid overflow (resp. wrap around)
  if (a > 1000000) {
    return 0;
  }

  b = 0;
  for (int i = 0; i < a; i++)  {
    if (nondet()) {
      b++;
    }
  }

  unsigned int c = a - b;
  if (c < 1) {
    return 0;
  }

  if (!(b < a)) {
    __VERIFIER_error();
  }
  return 0;
}
