//#Safe

/*
 * Taken from CBMC's regression test suite
 * (http://svn.cprover.org/svn/cbmc/trunk/regression/cbmc/).
 *
 * The overflow checks were omitted as these require more elaborate assertions.
 */

 extern void __VERIFIER_error(void);
int main()
{
  unsigned int i, j;
  double d;

  i=100.0;
  d=i;
  j=d;
  if(!(j==100)) __VERIFIER_error();
}
