extern void __VERIFIER_error(void);
/*
** largestSubnormalFloat.c
**
** Martin Brain
** martin.brain@cs.ox.ac.uk
** 25/07/12
**
*/

#include <math.h>

int main (void)
{
  #ifdef __GNUC__
  float largestSubnormalFloat = 0x1.fffffcp-127f;

  if(!(fpclassify(largestSubnormalFloat) != FP_NAN)) __VERIFIER_error();
  if(!(fpclassify(largestSubnormalFloat) != FP_INFINITE)) __VERIFIER_error();
  if(!(fpclassify(largestSubnormalFloat) != FP_ZERO)) __VERIFIER_error();
  if(!(fpclassify(largestSubnormalFloat) != FP_NORMAL)) __VERIFIER_error();
  if(!(fpclassify(largestSubnormalFloat) == FP_SUBNORMAL)) __VERIFIER_error();

  if(!(__fpclassifyf(largestSubnormalFloat) == FP_SUBNORMAL)) __VERIFIER_error();

  char b = isnormal(largestSubnormalFloat);

  if(!(!b)) __VERIFIER_error();
  #endif

  return 0;
}
