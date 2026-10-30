//#Unsafe
/*
  The loop body reads s and then gives it a value its formula does not constrain (in the integer translation an
  unsigned char is wrapped where it is used, not where it is assigned). The composed body therefore keeps s only as
  an inVar, i.e. havoced. k-induction used to keep such a variable unchanged and proved s == 0 inductive; the
  assertion fails in the second iteration.

  Author: Max Barth (max.barth95@gmx.de)
  Date: 2026-10-29
*/
extern unsigned char __VERIFIER_nondet_uchar(void);

int main(void) {
  unsigned char s = 0;
  while (1) {
    //@ assert s == 0;
    s = __VERIFIER_nondet_uchar();
  }
  return 0;
}
