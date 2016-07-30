extern void __VERIFIER_assume(int);
extern void __VERIFIER_error(void);
/*
** float-rounder-bug.c
**
** Martin Brain
** martin.brain@cs.ox.ac.uk
** 20/05/13
**
** Another manifestation of the casting bug.
** If the number is in (0,0x1p-126) it is rounded to zero rather than a subnormal number.
*/
#define FULP 1

void bug (float min) {
  __VERIFIER_assume(min == 0x1.fffffep-105f);
  float modifier = (0x1.0p-23 * (1<<FULP));
  float ulpdiff = min * modifier;

  if(!(ulpdiff == 0x1p-126f)) __VERIFIER_error();    // Should be true

  return;
}

void bugBrokenOut (float min) {
  __VERIFIER_assume(min == 0x1.fffffep-105f);
  float modifier = (0x1.0p-23 * (1<<FULP));
  double dulpdiff = (double)min * (double)modifier;  // Fine up to here
  float ulpdiff = (float)dulpdiff;  // Error

  if(!(ulpdiff == 0x1p-126f)) __VERIFIER_error(); // Should be true

  return;
}

void bugCasting (double d) {
  __VERIFIER_assume(d == 0x1.fffffep-127);

  float f = (float) d;

  if(!(f == 0x1p-126f)) __VERIFIER_error(); // Should be true

  return;
}

int main (void) {
  float f;
  bug(f);

  float g;
  bugBrokenOut(g);

  double d;
  bugCasting(d);

  return 1;
}

