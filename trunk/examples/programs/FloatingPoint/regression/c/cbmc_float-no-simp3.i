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

  float fs1=2.0f/6.0f;
  float fs2=fs1*6.0f;
  if(!((int)fs2==2)) __VERIFIER_error();
}