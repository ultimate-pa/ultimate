//#Safe

/*
 * Taken from CBMC's regression test suite
 * (http://svn.cprover.org/svn/cbmc/trunk/regression/cbmc/).
 *
 * The overflow checks were omitted as these require more elaborate assertions.
 */

 extern void __VERIFIER_error(void);

int main(void)
{
  float f = -0x1.0p-127f;
  double d = -0x1.0p-127;
  double fp = (double)f;

  if(!(d == fp)) __VERIFIER_error();

  return 0;
}
