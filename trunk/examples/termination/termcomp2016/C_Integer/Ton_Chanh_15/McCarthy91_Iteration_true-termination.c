//#termcomp16-someonesaidyes
/*
 * Date: 07/07/2015
 * Created by: Ton Chanh Le (chanhle@comp.nus.edu.sg)
 */

typedef enum {false, true} bool;

extern int __VERIFIER_nondet_int(void);

int main() {
  int c, n;
  c = 1;
  n = __VERIFIER_nondet_int();
  while (c > 0) {
    if (n > 100) {
      n = n - 10;
      c = c - 1;
    } else {
      n = n + 11;
      c = c + 1;
    }
  }
  return 0;
}
