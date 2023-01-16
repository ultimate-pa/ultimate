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
  float f;
  double d;
  unsigned char x;

  d=f;

  if(f==x)
    if(!(d==x)) __VERIFIER_error();
}
