//#Safe

/*
 * Taken from CBMC's regression test suite
 * (http://svn.cprover.org/svn/cbmc/trunk/regression/cbmc/).
 *
 * The overflow checks were omitted as these require more elaborate assertions.
 */

 extern void __VERIFIER_error(void);

int main (int argc, char **argv) {
  float f = 0x1.9e0c22p-101f;
  float g = -0x1.3c9014p-50f;
  float target = -0x1p-149f;

  float result = f * g;

  if(!(result == target)) __VERIFIER_error();

  return 0;
}
