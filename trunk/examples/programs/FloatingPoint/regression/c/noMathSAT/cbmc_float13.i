//#Safe

/*
 * Taken from CBMC's regression test suite
 * (http://svn.cprover.org/svn/cbmc/trunk/regression/cbmc/).
 *
 * The overflow checks were omitted as these require more elaborate assertions.
 */

 extern void __VERIFIER_error(void);

const float plus_infinity = 1.0f/0.0f;
const float minus_infinity = 0.0f/-0.0f;
const float NaN = 0.0f * (1.0f/0.0f);

int main()
{
  _Bool temp;


  temp = NaN < plus_infinity;
  if(!(!temp)) __VERIFIER_error();

  temp = NaN < minus_infinity;
  if(!(!temp)) __VERIFIER_error();

  temp = NaN <= NaN;
  if(!(!temp)) __VERIFIER_error();

  temp = NaN >= NaN;
  if(!(!temp)) __VERIFIER_error();

  temp = NaN > plus_infinity;
  if(!(!temp)) __VERIFIER_error();

  temp = NaN > minus_infinity;
  if(!(!temp)) __VERIFIER_error();

  temp = NaN > 0;
  if(!(!temp)) __VERIFIER_error();

  temp = NaN < 0;
  if(!(!temp)) __VERIFIER_error();

  return 0;
}
